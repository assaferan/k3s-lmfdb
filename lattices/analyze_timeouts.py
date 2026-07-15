#!/usr/bin/env python3
"""Post-run diagnostics: null-coverage + genus-fill / geometric failure counts.

The pipeline's TimeoutCall is silent on timeout, so failures are inferred from
the output: a definite genus with class_number = \\N means genus enumeration did
not complete (timeout or a Magma error), and \\N in a timeout-sensitive advanced
column means that geometric computation did not complete for that lattice.
"""
import sys
from pathlib import Path


def analyze_nulls(fmt_file, data_dir):
    cols = Path(fmt_file).read_text().strip().split("|")
    files = [p for p in Path(data_dir).rglob("*") if p.is_file()]
    n = len(files)
    if n == 0:
        print(f"  (no rows in {data_dir})")
        return
    nulls = [0] * len(cols)
    bad = 0
    for p in files:
        pieces = p.read_text().split("\n", 1)[0].split("|")
        if len(pieces) != len(cols):
            bad += 1
            continue
        for i, v in enumerate(pieces):
            if v == "\\N":
                nulls[i] += 1
    width = max(len(c) for c in cols)
    print(f"  {n} rows" + (f"  ({bad} with wrong field count!)" if bad else ""))
    for c, k in sorted(zip(cols, nulls), key=lambda x: -x[1]):
        if k == 0:
            continue
        flag = "  <-- ALL NULL" if k == n else ""
        print(f"  {c.ljust(width)}  {k:>7}  {k / n:>6.1%}{flag}")


def genus_fill(fmt_file, data_dir):
    """Count definite genera whose class_number is \\N (enumeration did not finish)."""
    cols = Path(fmt_file).read_text().strip().split("|")
    try:
        ci = cols.index("class_number")
    except ValueError:
        print("  (no class_number column)")
        return
    tot_def = fail_def = tot_indef = 0
    fails = []
    for p in Path(data_dir).rglob("*"):
        if not p.is_file():
            continue
        # path .../<rank>/<nplus>/<label>
        rank, nplus = int(p.parent.parent.name), int(p.parent.name)
        definite = rank == nplus
        val = p.read_text().split("\n", 1)[0].split("|")[ci]
        if definite:
            tot_def += 1
            if val == "\\N":
                fail_def += 1
                fails.append((rank, p.name))
        else:
            tot_indef += 1
    print(f"  definite genera:          {tot_def}")
    print(f"  indefinite genera:        {tot_indef}  (class_number N/A by design)")
    print(f"  definite w/ class_number=\\N (genus-fill did NOT complete): {fail_def}"
          f"  ({fail_def / tot_def:.2%} of definite)" if tot_def else "")
    if fails:
        byrank = {}
        for r, lab in fails:
            byrank.setdefault(r, []).append(lab)
        for r in sorted(byrank):
            print(f"    rank {r}: {len(byrank[r])}  e.g. {byrank[r][:3]}")


def joblogs():
    for name in ["fill", "tensor", "names", "connect"]:
        f = Path(f"{name}.joblog")
        if not f.exists():
            continue
        rows = [ln.split("\t") for ln in f.read_text().splitlines()[1:] if ln.strip()]
        n = len(rows)
        # joblog cols: Seq Host Starttime JobRuntime Send Receive Exitval Signal Command
        failed = [r for r in rows if len(r) > 6 and r[6] not in ("0", "")]
        times = [float(r[3]) for r in rows if len(r) > 3 and r[3]]
        mx = max(times) if times else 0
        print(f"  {name:8} jobs={n:5}  failed(exit!=0)={len(failed):3}  "
              f"max_runtime={mx:8.1f}s  total={sum(times):9.1f}s")
        for r in failed[:5]:
            print(f"      FAILED seq={r[0]} exit={r[6]} time={r[3]}s")


if __name__ == "__main__":
    print("=" * 70)
    print("GENUS-FILL COMPLETION (genera_advanced)")
    print("=" * 70)
    genus_fill("genera_advanced.format", "genera_advanced")
    print()
    print("=" * 70)
    print("JOBLOG SUMMARY")
    print("=" * 70)
    joblogs()
    print()
    print("=" * 70)
    print("LATTICE-LEVEL NULLS  (lattice_advanced_data)")
    print("=" * 70)
    analyze_nulls("lat_advanced.format", "lattice_advanced_data")
    print()
    print("=" * 70)
    print("LATTICE-LEVEL NULLS  (lattice_basic_data)")
    print("=" * 70)
    analyze_nulls("lat_basic.format", "lattice_basic_data")
