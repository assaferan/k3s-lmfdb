#!/usr/bin/env -S sage -python

import sys
import time
import argparse
import subprocess
import contextlib
from pathlib import Path
# Fully initialise Sage: under "sage -python" the lazy imports are not pre-resolved,
# which breaks genus enumeration in two ways on Sage 10.7 -- a missing
# laurent_polynomial_ring attribute (via discriminant_group(...).normal_form()),
# and a sage.symbolic.function circular import (via the genus mass computation).
import sage.all  # noqa: F401
from genus import write_all_of_sig_between_genera_basic

@contextlib.contextmanager
def timed(label):
    print(f"=== {label} ...", flush=True)
    t0 = time.monotonic()
    yield
    print(f"=== {label}: done in {time.monotonic() - t0:.1f}s", flush=True)

parser = argparse.ArgumentParser("run_all", description="Run the whole pipeline for generating lattice data")

# Bounds on rank and discriminant
parser.add_argument("-r", "--min-rank", type=int, default=1, help="Lower bound on rank")
parser.add_argument("-R", "--max-rank", type=int, default=32, help="Upper bound on rank")
parser.add_argument("-d", "--min-disc-ratio", type=int, default=0, metavar="C", help="Enumerate genera of discriminant more than C/rank")
parser.add_argument("-D", "--max-disc-ratio", type=int, default=32768, help="Enumerate genera of discriminant at most C/rank")
parser.add_argument("-k", "--nokthree", action="store_true", help="By default, we also enumerate genera of discriminant up to d/(22-n) for nminus=1 or 2.  This option turns that off")

# Parallelization
parser.add_argument("-j", "--jobs", type=int, default=128, help="Number of parallel processes to use")
parser.add_argument("-b", "--batch-mass", type=int, default=128, help="Batch genus enumeration instances together until the total mass exceeds this amount")

# Don't store too many lattices
parser.add_argument("--enum-masslimit", type=int, default=1000, help="If the mass of a genus is larger than this threshold, don't even try to enumerate lattices within")
parser.add_argument("--enum-timelimit", type=int, default=300, help="Maximum number of seconds to spend on enumerating a genus") # TODO: calibrate this based on how much time we want to spend
parser.add_argument("--enum-sizelimit", type=int, default=1000, help="For genera with class number larger than this, do not store individual lattices within the genus")
parser.add_argument("--enum-adjlimit", type=int, default=100, help="For genera with class number larger than this, do not compute the adjacency (Hecke) matrix (its cost is ~class_number^2, so it dominates fill for moderate class numbers at high rank)")

# Skip stages
parser.add_argument("--skip-list-genera", action="store_true", help="Assume that genera have already been listed")
parser.add_argument("--skip-enumerate-genera", action="store_true", help="Assume that genera have already been enumerated (implies skip-list-genera)")
parser.add_argument("--skip-embeddings", action="store_true", help="Do not compute primitive and K3 embedding data")
parser.add_argument("--skip-tensor", action="store_true", help="Do not compute tensor product decompositions")
parser.add_argument("--skip-names", action="store_true", help="Do not find lattice names")
parser.add_argument("--skip-connect", action="store_true", help="Do not run_connect_genus.m")

## TODO: Support building on partial progress by checking what files already exist, or by writing a json file that is updated with state

args = parser.parse_args()

def ranks():
    yield from range(args.min_rank, args.max_rank + 1)

def signatures():
    for r in ranks():
        yield from [(r - n_minus, n_minus) for n_minus in range(r//2+1)]

def split_interval(a, b, m, prefix=()):
    n = b - a + 1
    q, r = divmod(n, m)
    bounds = [a]
    for i in range(m):
        bounds.append(bounds[-1] + q + (1 if i < r else 0))
    return [prefix + (bounds[i], bounds[i+1] - 1) for i in range(m)]

def Dbound(sig):
    c = args.min_disc_ratio
    C = args.max_disc_ratio
    r = sum(sig)
    if not args.nokthree and (12 <= r <= 20) and (sig[1] in [1,2]):
        min_det = c // (22 - r) + 1
        max_det = C // (22 - r)
    else:
        min_det = c // r + 1
        max_det = C // r
    return min_det, max_det

def build_genus_inputs():
    inputs = []
    for sig in signatures():
        min_det, max_det = Dbound(sig)
        inputs_sig = split_interval(min_det, max_det, args.jobs, sig)
        inputs.extend(inputs_sig)
    return inputs

def build_enumeration_inputs(fname):
    m = 0
    M = args.batch_mass
    labels = []
    with open("genera_basic.format") as F:
        basic = F.read().strip().split("|")
        massi = basic.index("mass")
    def get_mass(path):
        with open(path) as F:
            pieces = F.read().strip().split("|")
            num, den = pieces[massi].strip("{}").split(",")
            return float(num) / float(den)
    total = 0
    with open(fname, "w") as Fout:
        for sig in signatures():
            r = sum(sig)
            nplus = sig[0]
            base = Path("genera_basic", str(r), str(nplus))
            if not base.is_dir():
                continue            # no genera enumerated for this signature
            for genus in base.iterdir():
                if r == nplus:
                    m += get_mass(genus)   # genus is already the full path from iterdir()
                else:
                    m += 1 # pretend indefinite genera have mass 1
                labels.append(genus.name)
                if m > M:
                    _ = Fout.write(":".join(labels) + "\n")
                    m = 0
                    labels = []
                    total += 1
        if m > 0 :
            _ = Fout.write(":".join(labels) + "\n")
            total += 1
    return total

def build_tensor_inputs(fname):
    total = 0
    with open(fname, "w") as Fout:
        for sig in signatures():
            r = sum(sig)
            nplus = sig[0]
            d, D = Dbound(sig)
            # TODO: run_tensor.m only takes D right now
            _ = Fout.write(f"{r}.{nplus}:{D}\n")
            total += 1
    return total

def parallel(jobfile, joblog, magma_args, colsep=None):
    cmd = ["parallel", "-j", str(args.jobs), "--joblog", joblog, "--eta", "-a", jobfile]
    if colsep is not None:
        cmd += ["--colsep", colsep]
    cmd += ["magma", "-b"] + magma_args
    # GNU parallel returns the number of failed jobs; don't abort the pipeline on
    # per-job failures -- log a warning and continue (the joblog records which
    # jobs failed so they can be retried).
    result = subprocess.run(cmd)
    if result.returncode != 0:
        print(f"  WARNING: {result.returncode} job(s) failed (see {joblog}); continuing", flush=True)

def main():
    if not args.skip_list_genera:
        inputs = build_genus_inputs()
        total = len(inputs)
        start_time = time.monotonic()
        print(f"Listing genera ({total} tasks)...")

        for i, res in enumerate(write_all_of_sig_between_genera_basic(inputs), 1):
            elapsed = time.monotonic() - start_time
            avg_time = elapsed / i
            eta = avg_time * (total - i)
            percent = (i / total) * 100

            # Build the bar string
            bar = "#" * int(percent // 5) + "-" * (20 - int(percent // 5))

            # Update the same line in stdout
            sys.stdout.write(f"\r|{bar}| {percent:.1f}% ({i}/{total}) | ETA: {eta:.1f}s")
            sys.stdout.flush()

        print(f"\nDone listing genera! ({time.monotonic() - start_time:.1f}s)")

    gcount = build_enumeration_inputs("genus_jobs.txt")
    if not args.skip_enumerate_genera:
        with timed(f"Enumerating genera ({gcount} batches)"):
            # Pass the enumeration guards through to FillGenus so a few pathological
            # high-rank genera can't dominate wall-clock (they otherwise run for hours):
            # skip enumerating past enum-masslimit, store genus-level data only past
            # enum-sizelimit, and cap per-genus wall-clock at enum-timelimit.
            parallel("genus_jobs.txt", "fill.joblog",
                     [f"masslimit:={args.enum_masslimit}", f"sizelimit:={args.enum_sizelimit}",
                      f"timelimit:={args.enum_timelimit}", f"adjlimit:={args.enum_adjlimit}",
                      "labels:={1}", "run_fill_genus.m"])

    if not args.skip_embeddings:
        print("Finding lattice embeddings (TODO: Oscar embedding code)")

    if not args.skip_tensor:
        tcount = build_tensor_inputs("tensor_jobs.txt")
        with timed(f"Computing tensor products ({tcount} tasks)"):
            parallel("tensor_jobs.txt", "tensor.joblog",
                     ["sig:={1}", "Dbound:={2}", "run_tensor.m"], colsep=":")

    if not args.skip_names:
        with timed("Computing basic names"):
            # Cap the named-lattice scalings at the determinant we actually enumerated
            # (otherwise NameAtomicLattices scans scalings up to its default 32768,
            # which for low ranks is tens of thousands of wasted FindLabel calls), and
            # split the catalog across workers -- naming is otherwise the only serial
            # stage.  Each worker writes atomic_names_partial_<k>; merge them keeping
            # the lowest-priority name per label (the same collision rule the intrinsic
            # applies in-process).
            with open("name_jobs.txt", "w") as Fout:
                for w in range(args.jobs):
                    Fout.write(f"{w}:{args.jobs}\n")
            parallel("name_jobs.txt", "names.joblog",
                     [f"DETCAP:={args.max_disc_ratio}", "WORKER:={1}", "NWORKERS:={2}", "run_basic_names.m"],
                     colsep=":")
            best = {}   # label -> (priority, name)
            for w in range(args.jobs):
                partial = Path(f"atomic_names_partial_{w}")
                if not partial.exists():
                    continue
                for line in partial.read_text().splitlines():
                    if not line:
                        continue
                    label, name, prio = line.rsplit("|", 2)
                    # match NameAtomicLattices' collision rule: (priority, name),
                    # lower priority wins, ties to the lexicographically smaller name
                    key = (int(prio), name)
                    if label not in best or key < best[label]:
                        best[label] = key
                partial.unlink()
            with open("atomic_names", "w") as Fout:
                Fout.write("\n".join(f"{label}|{name}" for label, (_, name) in best.items()))
            print(f"Named {len(best)} atomic lattices (merged from {args.jobs} workers).", flush=True)

    if not args.skip_connect:
        # Connect in two passes.  A decomposable lattice derives its geometric fields
        # (eutaxy, covering radius, deep holes, ...) from its orthogonal factors --
        # strictly lower-rank lattices in other genera whose data is written during
        # connect.  A single flat pass that processed a composite before its factors
        # silently dropped those fields to \N.  So: pass 1 ("produce") runs the full
        # connect for every genus but skips the decomposable derivations, which writes
        # every indecomposable factor's data to disk; pass 2 ("consume") then derives
        # the decomposable fields with all factor data guaranteed present.  Both passes
        # are flat and fully parallel; the only barrier is between them.
        with timed("Connecting genera (pass 1: produce)"):
            parallel("genus_jobs.txt", "connect1.joblog",
                     ["labels:={1}", "phase:=1", "run_connect_genus.m"])
        with timed("Connecting genera (pass 2: consume)"):
            parallel("genus_jobs.txt", "connect2.joblog",
                     ["labels:={1}", "phase:=2", "run_connect_genus.m"])

if __name__ == "__main__":
    main()
