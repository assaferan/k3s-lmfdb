#!/usr/bin/env python3
"""Report, per column, how many rows are still "\\N" (null) in the pipeline output.

Usage:
    python3 analyze_nulls.py [basic|advanced|both]   (default: both)

Reads the column names from lat_basic.format / lat_advanced.format and the rows
from lattice_basic_data/** and lattice_advanced_data/**, and prints for each
column the number and fraction of "\\N" values (and any all-null columns).
"""
import sys
from pathlib import Path


def analyze(fmt_file, data_dir):
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
    print(f"  {'column'.ljust(width)}  {'null':>7}  {'frac':>6}")
    for c, k in zip(cols, nulls):
        bar = "  <-- all null" if k == n else ("  <-- always set" if k == 0 else "")
        print(f"  {c.ljust(width)}  {k:>7}  {k / n:>6.1%}{bar}")


def main():
    which = sys.argv[1] if len(sys.argv) > 1 else "both"
    if which in ("basic", "both"):
        print("=== lattice_basic_data (lat_basic.format) ===")
        analyze("lat_basic.format", "lattice_basic_data")
    if which in ("advanced", "both"):
        print("=== lattice_advanced_data (lat_advanced.format) ===")
        analyze("lat_advanced.format", "lattice_advanced_data")


if __name__ == "__main__":
    main()
