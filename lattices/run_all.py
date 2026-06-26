#!/usr/bin/env -S sage -python

import sys
import time
import argparse
import subprocess
from pathlib import Path
from genus import write_all_of_sig_between_genera_basic

parser = argparse.ArgumentParser("run_all", description="Run the whole pipeline for generating lattice data")

# Bounds on rank and discriminant
parser.add_argument("-r", "--min-rank", type=int, default=1, description="Lower bound on rank")
parser.add_argument("-R", "--max-rank", type=int, default=32, description="Upper bound on rank")
parser.add_argument("-d", "--min-disc-ratio", type=int, default=0, metavar="C", description="Enumerate genera of discriminant more than C/rank")
parser.add_argument("-D", "--max-disc-ratio", type=int, default=32768, description="Enumerate genera of discriminant at most C/rank")
parser.add_argument("-k", "--nokthree", action="store_true", description="By default, we also enumerate genera of discriminant up to d/(22-n) for nminus=1 or 2.  This option turns that off")

# Parallelization
parser.add_argument("-j", "--jobs", type=int, default=128, description="Number of parallel processes to use")
parser.add_argument("-b", "--batch-mass", type=int, default=128, description="Batch genus enumeration instances together until the total mass exceeds this amount")

# Don't store too many lattices
parser.add_argument("--enum-masslimit", type=int, default=1000, description="If the mass of a genus is larger than this threshold, don't even try to enumerate lattices within")
parser.add_argument("--enum-timelimit", type=int, default=300, description="Maximum number of seconds to spend on enumerating a genus") # TODO: calibrate this based on how much time we want to spend
parser.add_argument("--enum-sizelimit", type=int, default=1000, description="For genera with class number larger than this, do not store individual lattices within the genus")

# Skip stages
parser.add_argument("--skip-list-genera", action="store_true", description="Assume that genera have already been listed")
parser.add_argument("--skip-enumerate-genera", action="store_true", description="Assume that genera have already been enumerated (implies skip-list-genera)")
parser.add_argument("--skip-embeddings", action="store_true", description="Do not compute primitive and K3 embedding data")
parser.add_argument("--skip-tensor", action="store_true", description="Do not compute tensor product decompositions")
parser.add_argument("--skip-names", action="store_true", description="Do not find lattice names")
parser.add_argument("--skip-connect", action="store_true", description="Do not run_connect_genus.m")

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
            return float(pieces[0]) / float(pieces[1])
    total = 0
    with open(fname, "w") as Fout:
        for sig in signatures():
            r = sum(sig)
            nplus = sig[0]
            base = Path("genera_basic", str(r), str(nplus))
            for genus in base.iterdir():
                if r == nplus:
                    m += get_mass(base / genus)
                else:
                    m += 1 # pretend indefinite genera have mass 1
                labels.append(genus.name)
                if m > M:
                    _ = Fout.write(":".join(labels))
                    m = 0
                    labels = []
                    total += 1
        if m > 0 :
            _ = Fout.write(":".join(labels))
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

def main():
    if not args.skip_list_genera:
        start_time = time.monotonic()
        total = len(inputs)
        inputs = build_genus_inputs()

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

        print("\nDone listing genera!")

    gcount = build_enumeration_inputs("genus_jobs.txt")
    if not args.skip_enumerate_genera:
        print("Enumerating genera ({gcount} tasks)...")
        # TODO: add progress bar, jobfile
        cmd = ["parallel", "-j", str(args.jobs), "-a", "genus_jobs.txt", "magma", "-b", "labels:={1}", "run_fill_genus.m"]
        subprocess.run(cmd, check=True)

    if not args.skip_embeddings:
        print("Finding lattice embeddings")
        # TODO: Figure out how to call Oscar embedding code

    if not args.skip_tensor:
        tcount = build_tensor_inputs("tensor_jobs.txt")
        print("Computing tensor products ({tcount} tasks)...")
        cmd = ["parallel", "-j", str(args.jobs), "-a", "tensor_jobs.txt", "--colsep", ":", "magma", "-b", "sig:={1}", "Dbound:={2}", "run_tensor.m"]
        subprocess.run(cmd, check=True)

    if not args.skip_names:
        cmd = ["magma", "-b", "run_basic_names.m"]
        print("Computing basic names")
        subprocess.run(cmd, check=True)

    if not args.skip_connect:
        cmd = ["parallel", "-j", str(args.jobs), "-a", "genus_jobs.txt", "magma", "-b", "labels:={1}", "run_connect_genus.m"]
        print("Connecting genera")
        subprocess.run(cmd, check=True)
