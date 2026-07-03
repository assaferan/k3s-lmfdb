// Computes tensor products of primitive lattices

intrinsic LabelsToDiscs(labels::SeqEnum[MonStgElt]) -> SeqEnum[RngIntElt]
{}
    return [StringToInteger(Split(label, ".")[3]) : label in labels];
end intrinsic;

intrinsic LoadTensorIndecomposables(sig::Tup, Dbound::RngIntElt) -> SeqEnum[Tup]
{
Load all lattices of a given signature and bounded absolute discriminant from disk.

WARNING: since this is designed to run as part of a large parallel process, this intrinsic
will WAIT for the necessary files to be written to disk rather than raising an error.
}
    while not OpenTest(Sprintf("tensor_indecomp/%o.%o.done", sig[1], sig[2]), "r") do
        Sleep(2);
    end while;
    labels := Split(Read(Sprintf("tensor_indecomp/%o.%o", sig[1], sig[2])), "\n");
    discs := LabelsToDiscs(labels);
    for i in [1..#discs] do
        if i gt 1 and discs[i] lt discs[i-1] then
            error "Labels not sorted";
        end if;
        if discs[i] gt Dbound then
            return [<labels[j], discs[j]> : j in [1..i-1]];
        end if;
    end for;
    error "Not enough indecomposables saved to guarantee completeness";
end intrinsic;

intrinsic SortLabels(~labels::SeqEnum[MonStgElt])
{}
    pieces := [Split(label, ".") : label in labels];
    pieces := [<StringToInteger(piece[1]), StringToInteger(piece[2]), StringToInteger(piece[3]), piece[4]> : piece in pieces];
    ParallelSort(~pieces, ~labels);
end intrinsic;

intrinsic TrimLabels(labels::SeqEnum[MonStgElt], Dbound::RngIntElt) -> SeqEnum[MonStgElt]
{}
    discs := LabelsToDiscs(labels);
    return [labels[i] : i in [1..#labels] | discs[i] le Dbound];
end intrinsic;

intrinsic LoadLatticeLabels(sig::Tup, Dbound::RngIntElt) -> SeqEnum[MonStgElt]
{}
    // must match the directory LabelPath("lattice_basic_data", label) writes into
    base := Sprintf("lattice_basic_data/%o/%o/", sig[1], sig[2]);   // sig = <rank, nplus>
    labels := TrimLabels(Split(Pipe("ls " * base, ""), "\n"), Dbound);
    SortLabels(~labels);
    return labels;
end intrinsic;

sig_cache := NewStore();

intrinsic SigCache() -> Assoc
{Get an associative array for caching all lattices of a given signature up to a discriminant bound}
    if not StoreIsDefined(sig_cache, "cache") then
        // NB: no Default -- a Default makes IsDefined(cache, k) return true for
        // every key, so LoadPrimitiveLattices would Explode an empty default.
        StoreSet(sig_cache, "cache", AssociativeArray());
    end if;
    return StoreGet(sig_cache, "cache");
end intrinsic;

intrinsic LoadPrimitiveLattices(sig::Tup, Dbound::RngIntElt) -> Assoc
{}
    cache := SigCache();
    if IsDefined(cache, sig) then
        curbound, lats := Explode(cache[sig]);
        if curbound eq Dbound then
            return lats;
        elif curbound gt Dbound then
            trimmed := AssociativeArray();
            for label -> L in lats do
                if StringToInteger(Split(label, ".")[3]) le Dbound then
                    trimmed[label] := L;
                end if;
            end for;
            return trimmed;
        end if;
        have := Keys(lats);
    else
        lats := AssociativeArray();
        have := {};
    end if;
    labels := LoadLatticeLabels(sig, Dbound);
    labels := [label : label in labels | label notin have];
    format := Split(Read("lat_basic.format"), "|");
    gram_i := Index(format, "gram");
    scale_i := Index(format, "scale");
    for label in labels do
        fname := LabelPath("lattice_basic_data", label);
        pieces := Split(Read(fname), "|");
        if pieces[scale_i] eq "1" then
            lats[label] := GramStringToLat(pieces[gram_i], sig[1]);   // sig = <rank, nplus>
        end if;
    end for;
    cache[sig] := <Dbound, lats>;
    StoreSet(sig_cache, "cache", cache);   // persist the cache across calls
    return lats;
end intrinsic;

intrinsic Factorizations(n::RngIntElt : lower:=2) -> SeqEnum[SeqEnum[RngIntElt]]
{Unordered factorizations of n into products of positive integers, each at least 2}
    facs := [[n]];
    M := [m : m in Divisors(n) | lower le m and m^2 le n];
    for m in M do
        for F in Factorizations((n div m) : lower:=m) do
            Append(~facs, F cat [m]);
        end for;
    end for;
    return Sort(facs);
end intrinsic;

intrinsic SigDiffFactorizations(n::RngIntElt, ranks::SeqEnum[RngIntElt]) -> SeqEnum[SeqEnum[RngIntElt]]
{Ordered factorizations of n into a product of #ranks integers, with the factor corresponding to r having the same parity as r and in the interval [0..r]}
    if #ranks eq 0 then
        if n eq 1 then
            return [[]];
        else
            return [];
        end if;
    end if;
    r := ranks[1];
    r2 := r mod 2;
    if #ranks eq 1 then
        if n mod 2 eq r mod 2 and 0 le n and n le r then
            return [[n]];
        else
            return [];
        end if;
    end if;
    ans := [];
    if n eq 0 then
        if r2 eq 0 then
            ans cat:= [[0] cat [x : x in F] : F in CartesianProduct([[rk mod 2..rk by 2] : rk in ranks[2..#ranks]])];
            r2 := 2;
        end if;
        for rk in [r2..r by 2] do
            ans cat:= [[rk] cat F : F in SigDiffFactorizations(0, ranks[2..#ranks])];
        end for;
    else
        if r2 eq 0 then
            if n mod 2 eq 1 then
                D := [];
            else
                D := [2*d : d in Divisors(n div 2) | 2*d le r];
            end if;
        else
            D := [d : d in Divisors(n div 2^Valuation(n, 2)) | d le r];
        end if;
        for d in D do
            ans cat:= [[d] cat F : F in SigDiffFactorizations(n div d, ranks[2..#ranks])];
        end for;
    end if;
    return ans;
end intrinsic;

intrinsic TensorSignatureSplits(sig::Tup) -> SeqEnum[SeqEnum[Tup]]
{All possible splits of a given signature into sequences of signatures whose tensor product matches the input}
    allsigs := [];
    for P in Factorizations(sig[1]) do
        for sigdiff in SigDiffFactorizations(2*sig[2] - sig[1], P) do
            sigs := [<P[i], (P[i] + sigdiff[i]) div 2> : i in [1..#P]];
            Append(~allsigs, sigs);
        end for;
    end for;
    return allsigs;
end intrinsic;

intrinsic TensorDecompositions(sigs::SeqEnum[Tup], Dbound::RngIntElt : recursing:=false) -> SeqEnum[Tup]
{
Find all decompositions of primitive lattices with absolute discriminant at most Dbound into indecomposable lattices so that the signatures of the indecomposable pieces are given in sigs.  <1,0> and <0,1> are not allowed for signatures.

For example, TensorDecomposition([<3,0>,<1,1>], 1000) will return the sequence of decompositions for lattices with signature <3,3> and absolute discriminant at most 1000 that decompose as a tensor product of an indecomposable lattice with signature <3,0> and an indecomposable lattice with signature <1,1>.

If recursing is false, the output is the sequence of tuples <label, decompositions>, where label is the label of the tensor product, decompositions is a nonempty sequence of decompositions of the given type, and no labels are repeated.
}
    if #sigs eq 0 then
        return [];
    end if;
    if #sigs eq 1 and not recursing then
        return [];
    end if;
    indecomp := LoadTensorIndecomposables(sigs[1], Dbound); // sorted by discriminant
    lats := LoadPrimitiveLattices(sigs[1], Dbound);
    if #sigs eq 1 then // automatically recursing
        return [<lats[pair[1]], [pair[1]], pair[2]> : pair in indecomp];
    end if;
    R := TensorDecompositions(sigs[2..#sigs], Dbound : recursing:=true); // sorted by discriminant
    ans := [];
    n1 := sigs[1][1];
    n2 := &+[sig[1] : sig in sigs[2..#sigs]];
    Ds := [];
    seen := {};
    for pair in indecomp do
        label, D1 := Explode(pair);
        decomp1 := [label];
        lat1 := lats[label];
        for trip in R do
            lat2, decomp2, D2 := Explode(trip);
            D := D1^n2 * D2^n1;
            if D gt Dbound then
                break;
            end if;
            decomp := decomp1 cat decomp2;
            SortLabels(~decomp);
            if decomp in seen then
                continue;
            end if;
            Include(~seen, decomp);
            lat := TensorProduct(lat1, lat2);
            if recursing then
                Append(~ans, <lat, decomp, D>);
                Append(~Ds, D);
            else
                Append(~ans, <FindLabel(lat), decomp>);
            end if;
        end for;
    end for;
    if recursing then
        ParallelSort(~Ds, ~ans);
    else
        // Need to collect by label
        A := AssociativeArray(:Default:=[]);
        for pair in ans do
            label, decomp := Explode(pair);
            Append(~A[label], decomp);
        end for;
        keys := [label : label in Keys(A)];
        SortLabels(~keys);
        ans := A;
    end if;
    return ans;
end intrinsic;

intrinsic TensorDecompositions(sig::Tup, Dbound::RngIntElt) -> Assoc, SetIndx[MonStgElt]
{
The output is an associative array, with keys the labels of the decomposable primitive lattices with this signature and values all of their decompositions into indecomposable lattices.  As a second return value, the indexed set of labels for primitive lattices of the given signature that do not admit a nontrivial decomposition of this form.
}
    lats := LoadPrimitiveLattices(sig, Dbound);
    indecomp := {label : label in Keys(lats)};
    decomp := AssociativeArray(:Default:=[]);
    n := sig[1];
    for sigs in TensorSignatureSplits(sig) do
        for label -> D in TensorDecompositions(sigs, Dbound) do
            Exclude(~indecomp, label);
            decomp[label] cat:= D;
        end for;
    end for;
    indecomp := [label : label in indecomp];
    SortLabels(~indecomp);
    return decomp, indecomp;
end intrinsic;
