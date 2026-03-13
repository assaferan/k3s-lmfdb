// This file is used to find the automorphism group of a lattice in a positive definite genus.
// Usage: magma -b label:=foo run_aut_grp.m
// Batch: magma -b labels:=foo:bar:baz run_aut_grp.m
//
// Parallel across servers:
//   xargs -n 100 < genera_todo.txt | tr ' ' ':' > genera_todo_chunked.txt
//   parallel --sshloginfile servers.txt --joblog jobs.log --eta --resume \
//     'cd ~/projects/k3s-lmfdb/lattices && magma -b labels:={} verbose:=0 run_aut_grp.m' \
//     :::: genera_todo_chunked.txt > output.txt
//
// Errors are prefixed with "ERROR: label: ..."
// Extract retry list: grep '^ERROR:' output.txt | cut -d: -f2 | tr -d ' ' > genera_failed.txt
// Check timings: cut -f 7 -d ' ' output.txt  | sort -n | tail

AttachSpec("lattices.spec");

if not assigned verbose then verbose := "0"; end if;
SetVerbose("FillGenus", StringToInteger(verbose));

if not assigned timeout then timeout := "60"; end if;
timeout := StringToInteger(timeout);

if assigned labels then
    label_list := Split(labels, ":");
else
    label_list := [label];
end if;

function automorphism_group(label : timeout := 1800, alg := AutomorphismGroup)
    label_components := Split(label, ".");
    n := StringToInteger(label_components[1]);
    s := StringToInteger(label_components[2]);
    error if n ne s, "Not positive definite";
    n_plus := (n + s) div 2;
    n_minus := (n - s) div 2;

    data := Split(Split(Read(Sprintf("genera_basic/sig_%o_%o/%o", n_plus, n_minus, label)), "\n")[1], "|");
    basic_format := Split(Read("genera_basic.format"), "|");
    assert #data eq #basic_format;
    basics := AssociativeArray();
    for i in [1..#data] do
        basics[basic_format[i]] := data[i];
        if data[i] eq "None" then basics[basic_format[i]] := "\\N"; end if;
    end for;
    
    n := StringToInteger(basics["rank"]);
    s := StringToInteger(basics["nplus"]);
    
    error if n ne s, "Not positive definite";

    K := Rationals();
    LWG := LatticeWithGram;
    rep := basics["rep"];
    // Switch to square brackets
    rep := "[" * rep[2..#rep - 1] * "]"; // Switch to square brackets
    gram := Matrix(K, n, eval rep);
    L := LWG(gram : CheckPositive := false);
    
    success, aut_group, elapsed := TimeoutCall(timeout, alg, <L>, 1);
    if success then
        printf "Automorphism group for %o computed in %o seconds\n", label, elapsed;
        aut_group := aut_group[1];
        return aut_group;
    end if;
    error if not success, "Failed to compute automorphism group for %o in %o seconds", label, elapsed;
end function;

procedure() // forcing magma to read the full input before forking
failed := [];
for l in label_list do
    try
        G := automorphism_group(l : alg := AutomorphismGroupFaster);
    catch e
        printf "ERROR: %o: %o\n", l, e;
        Append(~failed, l);
    end try;
end for;

if #failed gt 0 then
    exit 1;
end if;
exit 0;
end procedure();
