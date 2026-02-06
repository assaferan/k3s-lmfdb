// This file is used to find all of the representatives in a positive definite genus, along with some difficult to compute quantities about the genus itself.
// Usage: parallel -j 100 --timeout 1800 -a genera_todo.txt magma -b label:={} verbose:=1 run_fill_genus.m

AttachSpec("lattices.spec");

try
    // FillGenus(label : genus_reps_func := genus_reps);
    SetVerbose("FillGenus", 1);
    // Starting with a quick timeout to see if the code runs
    FillGenus(label : timeout := 60);
catch e
    E := Open("/dev/stderr", "a");
    Write(E, Sprint(e) cat "\n");
    Flush(E);
end try;
