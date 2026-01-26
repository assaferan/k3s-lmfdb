// This file is used to find all of the representatives in a positive definite genus, along with some difficult to compute quantities about the genus itself.
// Usage: parallel -j 100 --timeout 1800 -a genera_todo.txt magma -b label:={} fill_genus.m

// Todo: attach finite group code for IO.m and GroupToString
// AttachSpec("/Users/roed/sage/FiniteGroups/Code/spec");
AttachSpec("lattices.spec");

function hecke_primes(rank)
    if rank lt 8 then
        return [2,3,5];
    else
        return [2];
    end if;
end function;

function dict_to_jsonb(dict)
    return "{" * Join([Sprintf("%o:%o", key, dict[key]) : key in Keys(dict)], ",") * "}";
end function;

function to_postgres(val)
    if Type(val) in [SeqEnum, Tup] then
        return "{" * Join([Sprintf("%o",to_postgres(x)) : x in val],",") * "}";
    elif Type(val) eq Assoc then
        val_prime := AssociativeArray();
        for key in Keys(val) do
            val_prime[to_postgres(key)] := to_postgres(val[key]);
        end for;
        return dict_to_jsonb(val_prime);
    else
        return val;
    end if;
end function;

procedure fill_genus(label)
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
            hecke_mats[p] := to_postgres(Eltseq(Ap));
            hecke_polys[p] := to_postgres([(<Coefficients(pair[1]), pair[2]>) : pair in fpf]);
        end for;
        advanced["adjacency_matrix"] := dict_to_jsonb(hecke_mats);
        advanced["adjacency_polynomials"] := dict_to_jsonb(hecke_polys);
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
        if (n eq s) then 
            lat["gram"] := Eltseq(CanonicalForm(gram));
            A := AutomorphismGroup(L);
            lat["aut_size"] := #A;
            lat["festi_veniani_index"] := disc_aut_size div #A;
            if CanIdentifyGroup(#A) then
                Aid := IdentifyGroup(A);
                lat["aut_label"] := Sprintf("%o.%o", Aid[1], Aid[2]);
            else
                lat["aut_label"] := "\\N";
            end if;
            // This one needs David's code
            // lat["aut_group"] := GroupToString(A : use_id:=false);
            lat["aut_group"] := "\\N"; 
            lat["density"] := Density(L);
            lat["dual_density"] := Density(D);
            lat["hermite"] := HermiteNumber(L);
            lat["dual_hermite"] := HermiteNumber(D);
            lat["kissing"] := KissingNumber(L);
            lat["dual_kissing"] := KissingNumber(D);
            m := Minimum(L);
            lat["minimum"] := m;
            prec := Max(StringToInteger(basics["theta_prec"]), m+4);
            lat["theta_series"] := AbsEltseq(ThetaSeries(L, prec - 1));
            lat["theta_prec"] := prec;
            lat["dual_theta_series"] := AbsEltseq(ThetaSeries(D, prec - 1));
        else
            lat["gram"] := Eltseq(gram);
            // !!!  TODO - Need to be able to compute the automorphism group for non-definite lattices
            lat["aut_size"] := "\\N";
            lat["festi_veniani_index"] := "\\N";
            lat["aut_label"] := "\\N";
            lat["aut_group"] := "\\N";
            lat["density"] := "\\N";
            lat["dual_density"] := "\\N";
            lat["hermite"] := "\\N";
            lat["dual_hermite"] := "\\N";
            lat["kissing"] := "\\N";
            lat["dual_kissing"] := "\\N";
            lat["minimum"] := "\\N";
            lat["theta_series"] := "\\N";
            lat["theta_prec"] := "\\N";
            lat["dual_theta_series"] := "\\N";
        end if;
        
        lat["level"] := Level(LatticeWithGram(ChangeRing(GramMatrix(L), Integers()) : CheckPositive:=false));
        
        // Need dual_label, dual_conway
        // Compute festi_veniani_index in Sage?
        
        // TODO - do we also need these? or should we only keep them for the genus?
        lat["genus_label"] := basics["label"];
        lat["conway_symbol"] := basics["conway_symbol"];
        Append(~lats, lat);
    end for;

    function cmp_lat(L1, L2)
        d := L2["aut_size"] - L1["aut_size"];
        if (d ne 0) then return d; end if;
        prec := Minimum(L1["theta_prec"], L2["theta_prec"]);
        for i in [1..prec - 1] do
            d := L1["theta_series"][i] - L2["theta_series"][i];
            if (d ne 0) then return d; end if;
        end for;
        for i in [1..L1["rank"]^2] do
            d := Eltseq(L1["gram"])[i] - Eltseq(L2["gram"])[i];
            if (d ne 0) then return d; end if;
        end for;
        return 0;
    end function;

    // Tie breaker
      
    // Need dual_label, dual_conway
    // Compute festi_veniani_index in Sage?
    // Need label for lattice.  Don't want the label to rely on a difficult computation.  So we should probably avoid using the canonical form, and maybe avoid the automorphism group.
    // Proposal: Sort lexicographically by:
    // 1. Size of automorphism group (larger first): unfortunately this may be hard to compute
    // 2. Density
    // 3. theta series
    // 4. dual theta series
    // 5. arbitrary tiebreaker
    // TODO: Sort reps according to canonical form?
    if (n eq s) then
        lats := Sort(lats, cmp_lat);
    end if;

    for idx->L in lats do
        // Need label for lattice.
        lat := L;
        lat["label"] := Sprintf("%o.%o", basics["label"], idx);
        output := Join([Sprintf("%o", to_postgres(lat[k])) : k in lat_format], "|");
        Write("lattice_data/" * lat["label"], output : Overwrite);
    end for;

    output := Join([basics[k] : k in basic_format] cat [Sprintf("%o", advanced[k]) : k in advanced_format], "|");
    SetColumns(0);
    Write("genera_advanced/" * label, output : Overwrite);

end procedure;

fill_genus(label);
