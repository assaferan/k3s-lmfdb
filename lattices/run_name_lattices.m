// Stage 4 of the pipeline: fill the "name" field of the lattices.
//
// Run after run_connect_genus:
//   pass 0   -- name the atomic lattices: take Magma's LatticeDatabase lattices
//               (and their integral scalings) and locate each in our database via
//               its genus (NameAtomicLattices), rather than testing every lattice;
//   fixpoint -- name the decomposable lattices from their decompositions, tensor
//               products (preferred) then orthogonal sums, composing from the
//               names already assigned to the factors, until nothing changes.
// The names are written back into lattice_advanced_data (read-modify-write).
//
// Usage: magma -b [DETCAP:=N] run_name_lattices.m

AttachSpec("lattices.spec");

if not assigned DETCAP then DETCAP := "32768"; end if;   // matches parallel_run.py's C
DETCAP := StringToInteger(DETCAP);

// --- format column positions ---
advanced_format := Split(Split(Read("lat_advanced.format"), "\n")[1], "|");
name_i := Index(advanced_format, "name");
of_i   := Index(advanced_format, "orthogonal_factors");
om_i   := Index(advanced_format, "orthogonal_multiplicities");

// "{a,b,c}" / "\N" -> sequence of the comma-separated entries (labels contain no
// commas, so a flat split is safe).
function ParseArray(s)
    if s eq "\\N" or #s lt 2 then return []; end if;
    inner := Substring(s, 2, #s-2);
    if #inner eq 0 then return []; end if;
    return Split(inner, ",");
end function;

function Basename(path)
    pieces := Split(path, "/");
    return pieces[#pieces];
end function;

// Pass 0: name the atomic (database) lattices, catalog-driven via their genus.
names := NameAtomicLattices(DETCAP);   // label -> name

// Tensor-decomposition options, keyed by label (lattice_decomp_data has one file
// per signature, each line "label|tensor_decompositions|is_tensor_product").
tensor_options := AssociativeArray();
for f in Split(Pipe("ls lattice_decomp_data 2>/dev/null || true", ""), "\n") do
    if #f eq 0 then continue; end if;
    for line in Split(Read("lattice_decomp_data/" * f), "\n") do
        if #line eq 0 then continue; end if;
        parts := Split(line, "|");
        tensor_options[parts[1]] := ParseTensorDecompositions(parts[2]);
    end for;
end for;

// Enumerate the lattices from the advanced-data files (the ones we rewrite) and
// collect their orthogonal-factor labels for the composite naming below.
adv_paths := [ p : p in Split(Pipe("find lattice_advanced_data -type f 2>/dev/null || true", ""), "\n") | #p gt 0 ];
factors := AssociativeArray();   // label -> <orthogonal_factor_labels, multiplicities>
for path in adv_paths do
    adv := Split(Split(Read(path), "\n")[1], "|");
    factors[Basename(path)] := < ParseArray(adv[of_i]), [ StringToInteger(x) : x in ParseArray(adv[om_i]) ] >;
end for;

// Fixpoint: name decomposable lattices, tensor products preferred.
changed := true;
while changed do
    changed := false;
    for label in Keys(factors) do
        if IsDefined(names, label) then continue; end if;
        nm := "\\N";
        if IsDefined(tensor_options, label) then
            for opt in tensor_options[label] do
                nm := TensorProductName(opt, names);
                if nm ne "\\N" then break; end if;
            end for;
        end if;
        if nm eq "\\N" and #factors[label][1] gt 0 then
            nm := OrthogonalSumName(factors[label][1], factors[label][2], names);
        end if;
        if nm ne "\\N" then names[label] := nm; changed := true; end if;
    end for;
end while;

// Read-modify-write the name into lattice_advanced_data.
nnamed := 0;
for path in adv_paths do
    label := Basename(path);
    if not IsDefined(names, label) then continue; end if;
    adv := Split(Split(Read(path), "\n")[1], "|");
    adv[name_i] := names[label];
    Write(path, Join(adv, "|") : Overwrite);
    nnamed +:= 1;
end for;

printf "Named %o of %o lattices.\n", nnamed, #adv_paths;
exit;
