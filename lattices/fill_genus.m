declare verbose FillGenus, 1;

import "neighbours.mag" : neighbours;

function hecke_primes(rank)
    if rank lt 8 then
        return [2,3,5];
    else
        return [2];
    end if;
end function;

function dict_to_jsonb(dict)
    return "{" * Join([Sprintf("\"%o\":%o", key, dict[key]) : key in Keys(dict)], ",") * "}";
end function;

function to_postgres(val : jsonb_val := false)
    delims := jsonb_val select "[]" else "{}";
    if ISA(Type(val),Mtrx) then
        return to_postgres(Eltseq(val) : jsonb_val:=jsonb_val);
    elif val cmpeq "\\N" then
        return val;
    // I think this is unnecessary, and used to cause problems, so removing for now.
    //elif Type(val) eq MonStgElt then
    //    return "\"" * val * "\""; // This will fail if the string has quotes, but I don't think that's ever true for us.
    elif Type(val) in [SeqEnum, Tup] then
        return delims[1] * Join([Sprintf("%o",to_postgres(x : jsonb_val:=jsonb_val)) : x in val],",") * delims[2];
    elif Type(val) eq Assoc then
        val_prime := AssociativeArray();
        for key in Keys(val) do
            val_prime[to_postgres(key)] := to_postgres(val[key] : jsonb_val:=true);
        end for;
        return dict_to_jsonb(val_prime);
    else
        return val;
    end if;
end function;

function RescaledDualNF(L)
    Q := Rationals();
    K := BaseRing(L);
    B := ChangeRing(BasisMatrix(L),Q);
    M := ChangeRing(InnerProductMatrix(L),Q);
    F := ChangeRing(GramMatrix(L),Q);
    B := F^-1 * B;
    B := IntegralMatrix(B);
    B div:= GCD(Eltseq(B));
    F := B * M * Transpose(B);
    F, d := IntegralMatrix(F);
    g := GCD(Eltseq(F));
    F div:= g;
    M := (d/g) * M;
    return NumberFieldLattice(Rows(ChangeRing(B, K)) : InnerProduct := ChangeRing(M,K));
end function;

function genus_reps(L)
    if Type(L) eq LatNF then return GenusRepresentatives(L); end if;
    if IsOdd(L) then return GenusRepresentatives(L); end if;
    return Setseq(neighbours(L : thorough));
end function;

intrinsic FillGenus(label::MonStgElt : genus_reps_func := GenusRepresentatives, timeout := 1800)
{Fill the data for a genus and its lattice representatives, given files in the genera_basic format.}
    data := Split(Split(Read("genera_basic/" * label), "\n")[1], "|");
    basic_format := Split(Read("genera_basic.format"), "|");
    advanced_format := Split(Read("genera_advanced.format"), "|");
    lat_format := Split(Split(Read("lat.format"), "\n")[1], "|");
    assert #data eq #basic_format;
    basics := AssociativeArray();
    for i in [1..#data] do
        basics[basic_format[i]] := data[i];
        if data[i] eq "None" then basics[basic_format[i]] := "\\N"; end if;
    end for;
    advanced := AssociativeArray();
    lats := [];

    n := StringToInteger(basics["rank"]);
    s := StringToInteger(basics["signature"]);
    as_num := (s * (n - s) ne 0);
    if as_num then
        // assert n gt 2;
        K := RationalsAsNumberField();
        LWG := NumberFieldLatticeWithGram;
        DualLat := RescaledDualNF;
    else
        assert n eq s;
        K := Rationals();
        LWG := LatticeWithGram;
        DualLat := Dual; 
    end if;
    rep := basics["rep"];
    // Switch to square brackets
    rep := "[" * rep[2..#rep - 1] * "]"; // Switch to square brackets
    gram0 := Matrix(K, n, eval rep);
    L0 := LWG(gram0);
    // reps := GenusRepresentatives(L0);
    vprintf FillGenus, 1 : "Computing genus representatives...";
    reps := [];
    genus_success := false;
    if n ne 2 then
        genus_success, reps, elapsed := TimeoutCall(timeout, genus_reps_func, <L0>, 1);
        vprintf FillGenus, 1 : "Genus representatives computed in %o seconds\n", elapsed;
    end if;
    if genus_success then
        advanced["class_number"] := #reps;
        advanced["adjacency_matrix"] := "\\N";
        advanced["adjacency_polynomials"] := "\\N";
        vprintf FillGenus, 1 : "Computing adjacency matrix for p = ";
        hecke_mats := AssociativeArray();
        hecke_polys := AssociativeArray();
        G := Genus(L0);
        // This works for 2.28 - should be replaced by SetGenus in 2.29
        G`Representatives := reps;
        for p in hecke_primes(n) do
            vprintf FillGenus, 1 : "%o:", p;
            vtime FillGenus, 1 : Ap := AdjacencyMatrix(G,p);
            fpf := Factorization(CharacteristicPolynomial(Ap));
            hecke_mats[p] := Ap;
            hecke_polys[p] := [(<Coefficients(pair[1]), pair[2]>) : pair in fpf];
        end for;
        vprintf FillGenus, 1 : "Done!\n";
        advanced["adjacency_matrix"] := to_postgres(hecke_mats);
        advanced["adjacency_polynomials"] := to_postgres(hecke_polys);
    end if;
    disc_invs := basics["discriminant_group_invs"];
    disc_invs := "[" * disc_invs[2..#disc_invs-1] * "]"; // Switch to square brackets
    disc_invs := eval disc_invs;
    disc_aut_size := #AutomorphismGroup(AbelianGroup(disc_invs)); 

    if (n eq s) then
        vprintf FillGenus, 1 : "Computing canonical forms and automorphism groups for representative ";
    end if;

    for Li->L in reps do
        lat := AssociativeArray();
        for col in ["rank", "signature", "det", "disc", "discriminant_group_invs", "is_even"] do
            lat[col] := basics[col];
        end for;
        lat["genus_label"] := basics["label"];
        lat["class_number"] := advanced["class_number"];
        D := DualLat(L);
        lat["dual_det"] := Determinant(D);
        // At the moment we do not know the label for the dual
        lat["dual_label"] := "\\N";
        // TODO := The code for ConwaySymbol is currently in sage. 
        // The magma implemntation is in version 2.29 that has some bugs
        // This is no longer part of the lattice, only of the genus
        // lat["dual_conway"] := "\\N";
        lat["gram"] := "\\N";  
        lat["canonical_gram"] := "\\N";
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
        lat["successive_minima"] := "\\N";
        gram := GramMatrix(L);
        if (n eq s) then 
            // TODO : This is lossy - change later
            vprintf FillGenus, 1 : "%o", gram;
            success, canonical_gram, elapsed := TimeoutCall(timeout, CanonicalForm, <gram>, 1);
            vprintf FillGenus, 1 : "Canonical form computed in %o seconds\n", elapsed;
            if success then 
                lat["canonical_gram"] := Eltseq(canonical_gram);
            end if;
            success, aut_group, elapsed := TimeoutCall(timeout, AutomorphismGroup, <L>, 1);
            vprintf FillGenus, 1 : "Automorphism group computed in %o seconds\n", elapsed;
            if success then 
                lat["aut_group"] := GroupToString(aut_group : use_id:=false);
                lat["aut_size"] := #aut_group;
                lat["festi_veniani_index"] := #aut_group div disc_aut_size;
                if CanIdentifyGroup(#aut_group) then
                    Aid := IdentifyGroup(aut_group);
                    lat["aut_label"] := Sprintf("%o.%o", Aid[1], Aid[2]);
                end if;
            end if;
            lat["density"] := Density(L);
            lat["dual_density"] := Density(D);
            lat["hermite"] := HermiteNumber(L);
            lat["dual_hermite"] := HermiteNumber(D);
            lat["kissing"] := KissingNumber(L);
            lat["dual_kissing"] := KissingNumber(D);
            m := Minimum(L);
            lat["minimum"] := m;
            prec := Max(150, m+4);
            lat["theta_series"] := Eltseq(ThetaSeries(L, prec - 1));
            lat["theta_prec"] := prec;
            lat["dual_theta_series"] := Eltseq(ThetaSeries(D, prec - 1));
            minima, vecs := SuccessiveMinima(L); // for now we just throw vecs away
            lat["successive_minima"] := minima;
        else
            lat["gram"] := [Eltseq(gram)];
            // At the moment we do not have a notion of a canonical gram in the indefinite case
            // !!!  TODO - Need to be able to compute some things for indefinite lattices
        end if;
        lat["dual_label"] := "\\N"; // set in next stage
        lat["is_indecomposable"] := "\\N"; // set in next stage
        lat["is_additively_indecomposable"] := "\\N"; // set in next stage
        lat["orthogonal_factors"] := "\\N"; // set in next stage
        lat["orthogonal_multiplicities"] := "\\N"; // set in next stage
        lat["tensor_decompositions"] := "\\N"; // set in next stage
        lat["is_tensor_product"] := "\\N"; // set in next stage
        lat["root_sublattice"] := "\\N"; // set in next stage
        lat["root_complement"] := "\\N"; // set in next stage
        lat["even_sublattice"] := "\\N"; // set in next stage
        lat["even_complement"] := "\\N"; // set in next stage
        lat["norm1_sublattice"] := "\\N"; // set in next stage
        lat["norm1_complement"] := "\\N"; // set in next stage
        lat["Zn_complement"] := "\\N"; // set in next stage
        lat["name"] := "\\N"; // set in next stage

        lat["level"] := Level(LatticeWithGram(ChangeRing(GramMatrix(L), Integers()) : CheckPositive:=false));

        // TODO - do we also need these? or should we only keep them for the genus?
        lat["genus_label"] := basics["label"];
        lat["conway_symbol"] := basics["conway_symbol"];
        lat["dual_conway_symbol"] := basics["dual_conway_symbol"];
        Append(~lats, lat);
    end for;

    vprintf FillGenus, 1 : "Done!\n";

    function cmp_lat(L1, L2)
        d := L2["aut_size"] - L1["aut_size"];
        if (d ne 0) then return d; end if;
        prec := Minimum(L1["theta_prec"], L2["theta_prec"]);
        for i in [1..prec - 1] do
            d := L1["theta_series"][i] - L2["theta_series"][i];
            if (d ne 0) then return d; end if;
        end for;
        for i in [1..n^2] do
            d := L1["gram"][i] - L2["gram"][i];
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
    perm := [1..#lats];
    if (n eq s) then
        Sort(~lats, cmp_lat, ~perm);
    end if;

    SetColumns(0);
    for idx->L in lats do
        // Need label for lattice.
        lats[idx]["label"] := Sprintf("%o.%o", basics["label"], idx);
    end for;

    for idx->L in lats do
        lat := L;
        if genus_success and (n eq s) then
            pNeighbors := AssociativeArray();
            for p in hecke_primes(n) do
                // !!! TODO - check that permutation is applied in the right direction
                pNeighbors[p] := ["\"" * lats[j]["label"] * "\"" : j in [1..#lats] | hecke_mats[p][idx^perm,j^perm] ne 0];
            end for;
            lat["pneighbors"] := to_postgres(pNeighbors);
        else
            lat["pneighbors"] := "\\N";
        end if;
        Remove(~lat, "theta_prec");
        error if Keys(lat) ne Set(lat_format), [k : k in lat_format | k notin Keys(lat)], [k : k in Keys(lat) | k notin lat_format];
        output := Join([Sprintf("%o", to_postgres(lat[k])) : k in lat_format], "|");
        Write("lattice_data/" * lat["label"], output : Overwrite);
    end for;
    error if Keys(basics) ne Set(basic_format), [k : k in basic_format | k notin Keys(basics)], [k : k in Keys(basics) | k notin basic_format];
    error if Keys(advanced) ne Set(advanced_format), [k : k in advanced_format | k notin Keys(advanced)], [k : k in Keys(advanced) | k notin advanced_format];
    output := Join([basics[k] : k in basic_format] cat [Sprintf("%o", advanced[k]) : k in advanced_format], "|");
    Write("genera_advanced/" * label, output : Overwrite);
    return;
end intrinsic;
