# Run the pipeline to fill the genus and lattices
from genus import write_all_of_sig_between_genera_basic
from glob import glob
import os
from merge_files import merge_files

# creates file for copy_from to the lat_genera and lat_lattices_new tables
def run_pipeline(n_plus, n_minus, log_ub_det):
    ub_det = 10**log_ub_det
    write_all_of_sig_between_genera_basic(n_plus, n_minus, 1, ub_det)
    n = n_plus + n_minus
    sig = n_plus - n_minus
    todo_fname = f"genera_todo_{n_plus}_{n_minus}_1_{ub_det}.txt"
    if os.path.exists(todo_fname):
        os.remove(todo_fname)
    pwd = os.getcwd()
    os.chdir("genera_basic")
    fnames = []
    for t in range(1, log_ub_det+1):
        fnames += glob(f"{n}.{sig}." + t*"[0-9]" + ".*")
    fnames += glob(f"{n}.{sig}.1" + log_ub_det*"0" + ".*")
    os.chdir(pwd)
    with open(todo_fname, "a") as f:
        n_written = f.write("\n".join(fnames))
    outputs = f"outputs/{n_plus}_{n_minus}_1_{ub_det}"
    log = f"logs/{n_plus}_{n_minus}_1_{ub_det}.log"
    #cmd = f"parallel -j 100 --timeout 1800 -a genera_todo.txt --joblog {log} --results {outputs} magma -b label:={{}} verbose:=1 run_fill_genus.m"
    cmd = f"parallel -j 100 -a {todo_fname} --joblog {log} --results {outputs} magma -b label:={{}} verbose:=1 run_fill_genus.m"
    ret_val = os.system(cmd)
    fnames = []
    for t in range(1, log_ub_det+1):
        fnames += glob(f"genera_advanced/{n}.{sig}." + t*"[0-9]" + ".*")
    fnames += glob(f"genera_advanced/{n}.{sig}.1" + log_ub_det*"0" + ".*")
    merge_files(fnames, f"tables/genera_advanced_{n}_{sig}_1_{ub_det}.tbl")
    fnames = []
    for t in range(1, log_ub_det+1):
        fnames += glob(f"lattice_data/{n}.{sig}." + t*"[0-9]" + ".*")
    fnames += glob(f"lattice_data/{n}.{sig}.1" + log_ub_det*"0" + ".*")
    merge_files(fnames, f"tables/lattices_{n}_{sig}_1_{ub_det}.tbl", schema="lat")
    return

# if __name__ == "__main__":
#    run_pipeline(1, 1, 1, 1)
