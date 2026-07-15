// This script is used to find all of the representatives in a positive definite genus, along with some basic quantities of each lattice in the genus (roughly those that do not require access to lattices from any other genus) and some additional attributes of the genus itself.
// Usage: magma -b label:=foo run_fill_genus.m
// Batch: magma -b labels:=foo:bar:baz run_fill_genus.m
// Options: timeout:=N (default 60, seconds per label)
//
// Parallel across servers:
//   xargs -n 100 < genera_todo.txt | tr ' ' ':' > genera_todo_chunked.txt
//   parallel --sshloginfile servers.txt --joblog jobs.log --eta --resume \
//     'cd ~/projects/k3s-lmfdb/lattices && magma -b labels:={} verbose:=0 run_fill_genus.m' \
//     :::: genera_todo_chunked.txt > output.txt
//
// Errors are prefixed with "ERROR: label: ..."
// Extract retry list: grep '^ERROR:' output.txt | cut -d: -f2 | tr -d ' ' > genera_failed.txt

AttachSpec("lattices.spec");

if not assigned verbose then verbose := "0"; end if;
SetVerbose("FillGenus", StringToInteger(verbose));

if not assigned timeout then timeout := "60"; end if;
timeout := StringToInteger(timeout);

// Enumeration guards (0 = unlimited): see FillGenus.
if not assigned masslimit then masslimit := "0"; end if;
masslimit := StringToInteger(masslimit);
if not assigned sizelimit then sizelimit := "0"; end if;
sizelimit := StringToInteger(sizelimit);
if not assigned timelimit then timelimit := "0"; end if;
timelimit := StringToInteger(timelimit);
if not assigned adjlimit then adjlimit := "0"; end if;
adjlimit := StringToInteger(adjlimit);

if assigned labels then
    label_list := Split(labels, ":");
else
    label_list := [label];
end if;

procedure() // forcing magma to read the full input before forking
failed := [];
for l in label_list do
    try
        FillGenus(l : timeout := timeout, masslimit := masslimit, sizelimit := sizelimit, timelimit := timelimit, adjlimit := adjlimit);
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
