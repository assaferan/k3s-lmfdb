# Run the pipeline to fill the genus and lattices
from genus import write_all_of_sig_between_genera_basic
from glob import glob
import os
from merge_files import merge_files

# creates file for copy_from to the lat_genera and lat_lattices_new tables
def run_pipeline(n_plus, n_minus, lb_det, ub_det):
    write_all_of_sig_between_genera_basic(n_plus, n_minus, lb_det, ub_det)
    n = n_plus + n_minus
    sig = n_plus - n_minus
    os.remove("genera_todo.txt")
    for det in range(lb_det, ub_det+1):
        fnames = glob(f"genera_basic/{n}.{sig}.{det}.*")
        for fname in fnames:
            with open("genera_todo.txt", "a") as f:
                f.write(fname + "\n")
    cmd = f"parallel -j 100 --timeout 1800 -a genera_todo.txt magma -b label:={} verbose:=1 run_fill_genus.m"
    os.system(cmd)
    fnames = []
    for det in range(lb_det, ub_det+1):
        fnames += glob(f"genera_advanced/{n}.{sig}.{det}.*")
    merge_files(fnames, f"genera_advanced_{n}_{sig}_{lb_det}_{ub_det}.tbl")
    fnames = []
    for det in range(lb_det, ub_det+1):
        fnames += glob(f"lattice_data/{n}.{sig}.{det}.*")
    merge_files(fnames, f"lattices_{n}_{sig}_{lb_det}_{ub_det}.tbl", schema="lat")
    return

if __name__ == "__main__":
    run_pipeline(1, 1, 1, 1)