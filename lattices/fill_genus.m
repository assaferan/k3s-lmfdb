// This file is used to find all of the representatives in a positive definite genus, along with some difficult to compute quantities about the genus itself.
// Usage: parallel -j 100 --timeout 1800 -a genera_todo.txt magma -b label:={} fill_genus.m

// Todo: attach finite group code for IO.m and GroupToString
AttachSpec("/Users/roed/sage/FiniteGroups/Code/spec");

function hecke_primes(rank)
    if rank lt 8 then
        return [2,3,5];
    else
        return [2];
    end if;
end function;

data := Split(Read("genera_basic/" * label), "|");
basic_format := Split(Read("genera_basic.format"), "|");
advanced_format := Split(Read("genera_advanced.format"), "|");
lat_format := Split(Read("lat.format"), "|");
assert #data eq #basic_format;
basics := AssociativeArray();
for i in [1..#data] do
    basics[basic_format[i]] := data[i];
end for;
advanced := AssociativeArray();
lats := [];

n := StringToInteger(basics["rank"]);
s := StringToInteger(basics["signature"]);
as_num := (s * (n - s) ne 0);
if as_num then
    assert n gt 2;
    K := RationalsAsNumberField();
    LWG := NumberFieldLatticeWithGram;
else
    assert n eq s;
    K := Rationals();
    LWG := LatticeWithGram;
end if;
rep := basics["rep"];
// Switch to square brackets
rep := "[" * rep[2..#rep - 1] * "]"; // Switch to square brackets
gram0 := Matrix(K, n, eval rep);
L0 := LWG(gram0);
reps := GenusRepresentatives(L0);
advanced["class_number"] := #reps;
if n eq s then
    hecke_mats := AssociativeArray();
    hecke_polys := AssociativeArray();
    for p in hecke_primes(n) do
        Ap := AdjacencyMatrix(Genus(L0),p);
        fpf := Factorization(CharacteristicPolynomial(Ap));
        hecke_mats[p] := Eltseq(Ap);
        hecke_polys[p] := [<Coefficients(pair[1]), pair[2]> : pair in fpf];
    end for;
    advanced["adjacency_matrix"] := hecke_mats;
    advanced["adjacency_polynomials"] := hecke_polys;
else
    advanced["adjacency_matrix"] := "\\N";
    advanced["adjacency_polynomials"] := "\\N";
end if;
disc_invs := basics["discriminant_group_invs"];
disc_invs := "[" * disc_invs[2..#disc_invs-1] * "]"; // Switch to square brackets
disc_invs := eval disc_invs;
disc_aut_size := #AutomorphismGroup(AbelianGroup(disc_invs));

for L in reps do
    lat := AssociativeArray();
    for col in ["rank", "signature", "det", "disc", "discriminant_group_invs", "is_even"] do
        lat[col] := basics[col];
    end for;
    lat["class_number"] := advanced["class_number"];
    D := Dual(L);
    lat["dual_det"] := Determinant(D);
    gram := GramMatrix(L);
    lat["gram"] := Eltseq(gram);
    // Add canonical gram matrix
    // Any systematic way of producing names, or are we doing it manually?
    A := AutomorphismGroup(L);
    lat["aut_size"] := #A;
    if CanIdentifyGroup(#A) then
        Aid := IdentifyGroup(A);
        lat["aut_label"] := Sprintf("%o.%o", Aid[1], Aid[2]);
    else
        lat["aut_label"] := "\\N";
    end if;
    lat["aut_group"] := GroupToString(A : use_id:=false);
    lat["festi_veniani_index"] := "\\N";
    lat["density"] := Density(L);
    lat["dual_density"] := Density(D);
    lat["hermite"] := HermiteNumber(L);
    lat["dual_hermite"] := HermiteNumber(D);
    lat["kissing"] := KissingNumber(L);
    lat["dual_kissing"] := KissingNumber(D);
    m := Minimum(L);
    lat["minimum"] := m;
    prec := Max(StringToInteger(basics["theta_prec"]), m+4);
    lat["theta_series"] := Eltseq(ThetaSeries(L, prec - 1));
    lat["theta_prec"] := prec;
    lat["dual_theta_series"] := Eltseq(ThetaSeries(D, prec - 1));
    // Need dual_label, dual_conway
    // Compute festi_veniani_index in Sage?
    // Need label for lattice.
    Append(~lats, lat);
end for;



