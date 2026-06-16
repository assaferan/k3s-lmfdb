
intrinsic GramStringToLat(s::MonStgElt, n::RngIntElt) -> Lat
    gram := "[" * s[2..#s-1] * "]"; // Switch to square brackets
    gram := Matrix(Rationals(), n, eval gram);
    return LatticeWithGram(gram : CheckPositive := false);
end intrinsic;

function load_genus_data(genus_label)
    genus := AssociativeArray();
    for stage in ["basic", "advanced"] do
        genus_data := Split(Split(Read("genera_"*stage*"/" * label), "\n")[1], "|");
        genus_format := Split(Read("genera_"*stage*".format"), "|");
        assert #genus_data eq #genus_format;
        for i in [1..#genus_data] do
            genus[genus_format[i]] := genus_data[i];
            if genus_data[i] eq "None" then genus[genus_format[i]] := "\\N"; end if;
        end for;
    end for;
    return genus;
end function;

function lookup_hash_function(genus_hash) // TODO (David): the data needs to be written somewhere
    fname := Sprintf("genera_hash/%o", genus_hash);
    if not OpenTest(fname, "r") then
        return "";
    end if;
    return Read(fname);
end function;

hash_format := Split(Split(Read("lat_hash.format"), "\n")[1], "|");
function load_hash_data(genus_hash : as_assoc:=true)
    fname := Sprintf("lattice_hashes/%o", genus_hash); // TODO (David): should add folders
    if not OpenTest(fname, "r") then
        if as_assoc then return AssociativeArray(); else return []; end if;
    end if;
    hash_data := [Split(line, "|") : line in Split(Read(fname), "\n")];
    assert &and[#dat eq #hash_format : dat in hash_data];
    if as_assoc then
        hash_pos := Index(hash_format, "hash");
        lats := AssociativeArray(:Default:=[]);
        for lat in hash_data do
            h := StringToInteger(lat[hash_pos]);
            Append(~lats[h], lat);
        end for;
    else
        lats := [];
        for dat in hash_data do
            lat := AssociativeArray();
            for i in [1..#dat] do
                lat[hash_format[i]] := dat[i];
                if dat[i] eq "None" then lat[hash_format[i]] := "\\N"; end if;
            end for;
            Append(~lats, lat);
        end for;
    end if;
    return lats;
end function;

hash_cache := NewStore();

intrinsic HashCache() -> Assoc
{Get an associative array for caching lattices by genus and hash value}
    if not StoreIsDefined(hash_cache, "cache") then
        StoreSet(hash_cache, "cache", AssociativeArray(:Default:=AssociativeArray()));
    end if;
    return StoreGet(hash_cache, "cache");
end intrinsic;

intrinsic GetHashes(genus_hash::RngIntElt) -> Assoc
{Get an associative array with keys the possible hash values for lattices in the genus and values a sequence of strings matching the hash_format}
    cache := HashCache();
    if IsDefined(cache, genus_hash) then
        return cache[genus_hash];
    end if;
    lats := load_hash_data(genus_hash);
    cache[genus_hash] := lats;
    StoreSet(hash_cache, "cache", cache);
    return lats;
end intrinsic;

intrinsic FindGenusData(L::Lat) -> Tup
{Given a lattice, find the hash of its genus and the hash function used for that genus}
    genus_hash := HashGenus(L);
    hash_func := lookup_hash_function(genus_hash);
    return <genus_hash, hash_func>;
end intrinsic;

intrinsic FindLabel(L::Lat : genus_data:=<>) -> MonStgElt
{Given a lattice, find its label (or null if not in database)}
    if #genus_data eq 0 then
        genus_data := FindGenusData(L);
    end if;
    genus_hash, hash_func := Explode(genus_data);
    by_hash := GetHashes(genus_hash);
    if #by_hash eq 0 then
        // No lattices stored for this genus
        return "\\N";
    elif #by_hash eq 1 then
        poss := Values(by_hash)[1];
    else
        h := HashLat(L, genus_hash, hash_func);
        poss := by_hash[h];
    end if;
    if #poss eq 1 then
        found := poss[1];
    else
        n := Rank(L);
        gram_pos := Index(hash_format, "gram");
        found := [];
        for lat in poss do
            M := GramStringToLat(lat[gram_pos], n);
            if IsIsomorphic(L, M) then
                found := lat;
                break;
            end if;
        end for;
        assert #found ne 0;
    end if;
    label_pos := Index(hash_format, "label");
    return found[label_pos];
end intrinsic;

intrinsic LatSortKey(label::MonStgElt) -> Tup
{A tuple that sorts how we want lattices to sort}
    pieces := Split(label, ".");
    // Sort by: rank, then signature (pos def first), then absolute det, then the label string as tiebreaker
    return <StringToInteger(pieces[1]), -StringToInteger(pieces[2]), StringToInteger(pieces[3]), label>;
end intrinsic;

intrinsic AutOrbits(A::GrpMat, vecs::SeqEnum) -> SeqEnum
{Given an automorphism group and a sequence of vectors which is invariant under the action of A(which could be LatElts or ModTupFldElts), return orbit representatives for the action of A on vecs}
    // This assumes A is in GL_n(Z), with respect to the basis of the lattice
    // created with NaturalAction = false
    Sn := Sym(#vecs);
    perms := [Sn![Index(vecs, Coordelt(L,Eltseq(Vector(Coordinates(v))*g)))
		 : v in vecs] : g in Generators(A)];
    A_perm := sub<Sn|perms>;
    orb_reps := OrbitRepresentatives(A_perm);
    // We throw away the orbit sizes, and replace the index of the
    // representative by the representative itself
    return [vecs[o[2]] : o in orb_reps];
end intrinsic;

intrinsic VoronoiData(L::Lat, A::GrpMat) -> FldRatElt, SeqEnum[ModTupFldElt], RngIntElt, RngIntElt, RngIntElt
{Given a lattice L and its automorphism group A, find the covering norm, orbit representatives for the deep holes, the number of deep holes, the number of deep hole orbits, and the number of holes}
    cn := CoveringRadius(L);
    dh := DeepHoles(L);
    reps := AutOrbits(A, dh);
    return cn, reps, #dh, #reps, #Holes(L);
end intrinsic;

intrinsic IsWellRounded(L::Lat, S::SeqEnum) -> BoolElt
{Given the sequence of shortest vectors in a lattice, test if the lattice is well rounded (ie the rank of their span is equal to the rank of the lattice)}
    return "\\N"; // TODO (Eran)
end intrinsic;

intrinsic IsStronglyWellRounded(L::Lat, S::SeqEnum) -> BoolElt
{Given the sequence of shortest vectors in a lattice, test if it contains a basis for the lattice}
    return "\\N"; // TODO (Eran)
end intrinsic;

intrinsic IsMinimalVectorGenerated(L::Lat, S::SeqEnum) -> BoolElt
{Given the sequence of shortest vectors in a lattice, test if the lattice is generated by its minimal vectors}
    return "\\N"; // TODO (Eran)
end intrinsic;

intrinsic IsEutactic(L::Lat, S::SeqEnum) -> BoolElt
{Given the sequence S of shortest vectors in a lattice, test if the quadratic form x.x is a linear combination of the (x.s)^2, for s in S, with positive coefficients}
    return "\\N"; // TODO (Eran)
end intrinsic;

intrinsic tDesign(L::Lat, S::SeqEnum) -> RngIntElt
{Given the sequence S of shortest vectors in a lattice, find the largest even integer t such that S is a spherical t-design (sum_{s in S} (x.s)^t = C * x.x^(t/2) for some C, which must be (min(L) #S)/n).}
    return "\\N"; // TODO (Eran)
end intrinsic;

intrinsic LoadVdat(labels::SeqEnum[MonStgElt]) -> SeqEnum[Tup]
{Given a sequence of lattice labels, load Voronoi data as a sequence of tuples (covering norm, num deep holes, num deep hole orbits, num holes).  If any not available, return empty sequence instead}
    return []; // TODO (David)
end intrinsic;

intrinsic TimeoutAssign(~D::Assoc, key::MonStgElt, func::UserProgram, inp::Tup, timeout::RngIntElt)
{Compute value using given function, then store in D}
    success, out, elapsed := TimeoutCall(timeout, func, inp, 1);
    if success then
        D[key] := out[1];
    else
        D[key] := "\\N";
    end if;
end intrinsic;

intrinsic ConnectGenus(label::MonStgElt : timeout := 1800)
{Fill in lattice data that requires working with lattices in different genera}
    SetColumns(0);
    advanced_format := Split(Split(Read("lat_advanced.format"), "\n")[1], "|");
    genus := load_genus_data(label);
    n := StringToInteger(genus["rank"]);
    s := StringToInteger(genus["nplus"]);
    scale := StringToInteger(genus["scale"]);
    lats := load_hash_data(label : as_assoc:=false);
    if #lats gt 0 then
        to_per_rep := timeout div #lats + 1;
    end if;

    for i in [1..#lats] do
        lat := lats[i];
        L := GramStringToLat(lat["gram"], n);
        D := Dual(L);
        m := Minimum(D);
        target_prec := Max(150, m+4);

        lat["dual_det"] := Determinant(D);
        lat["dual_label"] := FindLabel(D);
        lat["dual_density"] := Density(D);
        lat["dual_hermite"] := HermiteNumber(D);
        lat["dual_kissing"] := KissingNumber(D);
        dual_theta, dual_theta_prec := ThetaSeriesIncremental(D, target_prec, to_per_rep);
        if dual_theta_prec gt 0 then
            lat["dual_theta_series"] := dual_theta;
            lat["dual_theta_prec"] := dual_theta_prec;
        else
            lat["dual_theta_series"] := [1];
            lat["dual_theta_prec"] := 1;
        end if;

        lat["is_universal"] := "\\N";
        lat["is_even_universal"] := "\\N";
        lat["is_regular"] := "\\N";
        lat["universality"] := "\\N";
        lat["even_universality"] := "\\N";
        lat["regularity"] := "\\N";

        // TODO (David): use 15/290 theorem and theta series to compute is_universal, is_even_univeral
        // TODO (David): use theta series to guess is_regular
        // TODO (David): use embedding data to compute universality, even_universality, regularity

        if scale eq 1 then
            lat["primitive_scaling"] := "\\N";
        else
            lat["primitive_scaling"] := FindLabel(LatticeWithGram(GramMatrix(L) div scale));
        end if;

        summands := OrthogonalDecompositionFaster(L);
        lat["is_indecomposable"] := (#summands eq 1);
        summand_labels := [FindLabel(M) : M in summands];
        collected := CountFibers(summand_labels, LatSortKey);
        lat["name"] := "\\N"; // TODO
        lat["orthogonal_factors"] := [fib[1][4] : fib in collected];
        lat["orthogonal_multiplicities"] := [fib[2] : fib in collected];

        for col in ["covering_norm", "deep_holes", "deep_hole_count", "deep_hole_orbit_count", "hole_count"] do
            lat[col] := "\\N"; // Overwritten below if possible
        end for;
        for col in ["shortest", "is_well_rounded", "is_minimal_vector_generated", "is_strongly_well_rounded", "is_eutactic", "t_design", "perfection_defect", "is_perfect"] do
            lat[col] := "\\N"; // Overwritten below if possible
        end for;
        if lat["is_indecomposable"] then
            // In addition to the timeout, we may want to impose a rank limit
            success, vdat, elapsed := TimeoutCall(timeout, VoronoiData, <L, aut_group>, 5);
            if success then
                lat["covering_norm"], lat["deep_holes"], lat["deep_hole_count"], lat["deep_hole_orbit_count"], lat["hole_count"] := Explode(vdat); // TODO (David): covering norm can be rational; need to update schema and saving process
            end if;

            // success, S, elapsed := TimeoutCall(timeout, ShortestVectors, <L>, 1); // TODO (Eran)
            success := false;
            if success then
                S := S[1];
                TimeoutAssign(~lat, "shortest", AutOrbits, <aut_group, S>, timeout);
                TimeoutAssign(~lat, "is_well_rounded", IsWellRounded, <L, S>, timeout);
                TimeoutAssign(~lat, "is_minimal_vector_generated", IsMinimalVectorGenerated, <L, S>, timeout);
                TimeoutAssign(~lat, "is_strongly_well_rounded", IsStronglyWellRounded, <L, S>, timeout);
                TimeoutAssign(~lat, "is_eutactic", IsEutactic, <L, S>, timeout);
                TimeoutAssign(~lat, "t_design", tDesign, <L, S>, timeout);
                TimeoutAssign(~lat, "perfection_defect", PerfectionDefect, <L, S>, timeout);
                if lat["perfection_defect"] cmpeq "\\N" then
                    lat["is_perfect"] := "\\N";
                else
                    lat["is_perfect"] := (lat["perfection_defect"] eq 0);
                end if;
            end if;
        else
            vdat := LoadVdat(lat["orthogonal_factors"]);
            if #vdat gt 0 then
                cnorm := 0;
                num_deep_holes := 1;
                num_deep_hole_orbits := 1;
                num_holes := 1;
                for i in [1..#vdat] do
                    cn, ndh, ndho, nh := Explode(vdat[i]);
                    m := lat["orthogonal_multiplicities"][i];
                    cnorm +:= m * cn;
                    num_deep_holes *:= ndh^m;
                    num_deep_hole_orbits *:= Binomial(ndho + m - 1, m);
                    num_holes *:= nh^m;
                end for;
                lat["covering_norm"] := cn;
                lat["deep_hole_count"] := num_deep_holes;
                lat["deep_hole_orbit_count"] := num_deep_hole_orbits;
                lat["hole_count"] := num_holes;
            end if;
        end if;

        lat["is_additively_indecomposable"] := "\\N"; // TODO
        lat["tensor_decompositions"] := "\\N"; // TODO (David)
        lat["is_tensor_product"] := "\\N"; // TODO (David)

        if lat["is_even"] then
            lat["even_sublattice"] := "\\N";
        else
            lat["even_sublattice"] := FindLabel(EvenSublattice(L));
        end if;

        sv1 := ShortVectors(L, 1, 1);
        R1 := sub<L|[x[1] : x in sv1]>;
        lat["norm1_rank"] := Rank(R1);
        if Rank(R1) eq 0 or Rank(R1) eq n then
            lat["norm1_complement"] := "\\N";
        else
            lat["norm1_complement"] := FindLabel(OrthogonalComplementFaster(L, R1)); // TODO (Eran): Make OrthogonalComplementFaster work for lattices
        end if;

        sv2 := ShortVectors(L, 1, 2);
        R := sub<L|[x[1] : x in sv2]>;
        lat["root_sublattice"] := RootString(R); // TODO (Eran)
        if Rank(R) eq 0 or Rank(R) eq n then
            lat["root_complement"] := "\\N";
        else
            lat["root_complement"] := FindLabel(OrthogonalComplementFaster(L, R));
        end if;

        lat["is_algebraic"] := "\\N"; // TODO

        // Remove gram since it's not in lat_advanced.format
        Remove(~lat, "gram");
        error if Keys(lat) ne Set(advanced_format), [k : k in advanced_format | k notin Keys(lat)], [k : k in Keys(lat) | k notin advanced_format];
        output := Join([Sprintf("%o", to_postgres(lat[k])) : k in advanced_format], "|");
        Write("lattice_advanced_data/" * lat["label"], output : Overwrite);
    end for;
end intrinsic;
