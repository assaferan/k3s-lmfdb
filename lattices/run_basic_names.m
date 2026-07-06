// Stage 4a of the pipeline: name the atomic lattices.
//
//   magma -b [DETCAP:=N] run_basic_names.m                       (serial)
//   magma -b [DETCAP:=N] WORKER:=k NWORKERS:=m run_basic_names.m (one parallel worker)
//
// Takes Magma's LatticeDatabase lattices (and their integral scalings up to
// determinant DETCAP) and locates each in our database via its genus, producing
// a global label -> name map for the atomic lattices.  ConnectGenus reads it and,
// in its per-lattice loop, sets each lattice's name to its atomic name or, for
// decomposable lattices, composes it from the names of its factors.
//
// Serial mode writes "atomic_names" (one "label|name" per line).  Worker mode
// (WORKER/NWORKERS) processes a slice of the catalog and writes a partial file
// "atomic_names_partial_<WORKER>" ("label|name|priority" per line); run_all.py
// merges the partials into "atomic_names", keeping the lowest-priority name per
// label (the same collision rule NameAtomicLattices uses in-process).

AttachSpec("lattices.spec");

if not assigned DETCAP then DETCAP := "32768"; end if;   // matches parallel_run.py's C
DETCAP := StringToInteger(DETCAP);

if assigned WORKER and assigned NWORKERS then
    worker := StringToInteger(WORKER);
    nworkers := StringToInteger(NWORKERS);
    names, prio := NameAtomicLattices(DETCAP : worker:=worker, nworkers:=nworkers);
    lines := [ Sprintf("%o|%o|%o", label, names[label], prio[label]) : label in Keys(names) ];
    Write("atomic_names_partial_" * WORKER, Join(lines, "\n") : Overwrite);
    printf "Worker %o/%o named %o atomic lattices.\n", worker, nworkers, #lines;
else
    names := NameAtomicLattices(DETCAP);
    lines := [ Sprintf("%o|%o", label, names[label]) : label in Keys(names) ];
    Write("atomic_names", Join(lines, "\n") : Overwrite);
    printf "Named %o atomic lattices (written to atomic_names).\n", #lines;
end if;
exit;
