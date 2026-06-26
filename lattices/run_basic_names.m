// Stage 4a of the pipeline: name the atomic lattices (serial, run once).
//
//   magma -b [DETCAP:=N] run_basic_names.m
//
// Takes Magma's LatticeDatabase lattices (and their integral scalings up to
// determinant DETCAP) and locates each in our database via its genus, producing
// a global label -> name map for the atomic lattices.  The map is written to the
// file "atomic_names" (one "label|name" per line); ConnectGenus reads it and,
// in its per-lattice loop, sets each lattice's name to its atomic name or, for
// decomposable lattices, composes it from the names of its factors.

AttachSpec("lattices.spec");

if not assigned DETCAP then DETCAP := "32768"; end if;   // matches parallel_run.py's C
DETCAP := StringToInteger(DETCAP);

names := NameAtomicLattices(DETCAP);

lines := [ Sprintf("%o|%o", label, names[label]) : label in Keys(names) ];
Write("atomic_names", Join(lines, "\n") : Overwrite);

printf "Named %o atomic lattices (written to atomic_names).\n", #lines;
exit;
