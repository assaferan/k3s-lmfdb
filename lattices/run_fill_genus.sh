#!/bin/bash
# Wrapper around magma run_fill_genus.m that reliably detects failures.
# Magma segfaults can report exit code 0 over SSH, so we verify that
# the "DONE" sentinel was printed, which only happens if Magma reaches
# the end of run_fill_genus.m without crashing.
#
# Usage (single label):
#   ./run_fill_genus.sh LABEL [VERBOSE] [TIMEOUT]
#
# Usage with GNU Parallel (use --resume-failed, not --resume):
#   parallel --sshloginfile servers.txt --joblog jobs.log --eta --resume-failed \
#     'cd ~/projects/k3s-lmfdb/lattices && ./run_fill_genus.sh {}' \
#     :::: labels.txt

set -u

label="$1"
verbose="${2:-0}"
timeout="${3:-60}"

cd "$(dirname "$0")" || exit 1

tmpout=$(mktemp)
trap 'rm -f "$tmpout"' EXIT

magma -b labels:="$label" verbose:="$verbose" timeout:="$timeout" done:=1 run_fill_genus.m 2>&1 | tee "$tmpout" | grep -v '^DONE'
ret=${PIPESTATUS[0]}

if [ $ret -ne 0 ]; then
    exit $ret
fi

# Magma segfaults can exit 0 over SSH; check for the sentinel
if ! grep -q '^DONE' "$tmpout"; then
    echo "WRAPPER_ERROR: $label: magma exited 0 but no DONE sentinel (likely segfault)" >&2
    exit 1
fi

exit 0
