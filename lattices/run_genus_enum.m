// This file is used to find all of the representatives in a positive definite genus.
// Usage: magma -b label:=foo run_genus_enum.m
// Batch: magma -b labels:=foo:bar:baz run_genus_enum.m
//
// Parallel across servers:
//   xargs -n 100 < genera_todo.txt | tr ' ' ':' > genera_todo_chunked.txt
//   parallel --sshloginfile servers.txt --joblog jobs.log --eta --resume \
//     'cd ~/projects/k3s-lmfdb/lattices && magma -b labels:={} verbose:=0 run_genus_enum.m' \
//     :::: genera_todo_chunked.txt > output.txt
//
// Errors are prefixed with "ERROR: label: ..."
// Extract retry list: grep '^ERROR:' output.txt | cut -d: -f2 | tr -d ' ' > genera_failed.txt
// Check timings: cut -f 7 -d ' ' output.txt  | sort -n | tail

AttachSpec("lattices.spec");

if assigned labels then
    label_list := Split(labels, ":");
else
    label_list := [label];
end if;

if not assigned verbose then verbose := "0"; end if;
SetVerbose("FillGenus", StringToInteger(verbose));

if not assigned timeout then timeout := "60"; end if;
timeout := StringToInteger(timeout);

function representatives(label : timeout := 1800, alg := GenusRepresentatives)
    data := Split(Split(Read("genera_basic/" * label), "\n")[1], "|");
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
    
    success, reps, elapsed := TimeoutCall(timeout, alg, <L>, 1);
    if success then
        printf "Genus representativesfor %o computed in %o seconds\n", label, elapsed;
        reps := reps[1];
        return reps;
    end if;
    error if not success, "Failed to enumerate genus representatives for", label, "in", elapsed, "seconds";
end function;

procedure() // forcing magma to read the full input before forking
failed := [];
for l in label_list do
    try
        reps := representatives(l : alg := GenusRepresentativesFaster);
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
