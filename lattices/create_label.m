// Functions to create the label for the genus in magma
// Note - needs functionality that is only introduced in Magma 2.29 

// Helper: base-62 digit for a nonnegative integer rank r (0..61)
function EncodeRank(r)
    error if r ge 0 and r lt 62,
        "rank must be in [0..61]";
    if r lt 10 then
        return IntegerToString(r);
    elif r lt 36 then
        // 'a'..'z' for 10..35
        return Sprintf("%c", StringToCode("a")[1] + (r - 10));
    else
        // 'A'..'Z' for 36..61
        return Sprintf("%c", StringToCode("A")[1] + (r - 36));
    end if;
end function;

// Helper: little-endian binary digits of n with exact width w
function DigitsLSB(n, w)
    bits := [];
    for i in [0..w-1] do
        Append(~bits, (n div 2^i) mod 2);
    end for;
    return bits;
end function;

function LocalSymbol(G,p)
    for s in LocalGenera(G) do
        if Prime(s) eq p then
            return s;
        end if;
    end for;
end function;

function SymbolTupleList(Gp)
    if Prime(Gp) eq 2 then
        return [<Gp`Valuations[i], Gp`Ranks[i], Gp`Determinants[i], Gp`Parities[i], Gp`Oddities[i]> : i in [1..#Gp`Valuations]];
    end if;
    return [<Gp`Valuations[i], Gp`Ranks[i], Gp`Determinants[i]> : i in [1..#Gp`Valuations]];
end function;

// Translate of Python create_genus_label
// Expects genus_sym to provide:
//   Rank(genus_sym), Signature(genus_sym), Determinant(genus_sym)
//   LocalSymbol(genus_sym, p) with methods:
//     NumberOfBlocks(), Trains(), Compartments(), CanonicalSymbol(), SymbolTupleList()
// CanonicalSymbol() is assumed to be a seq of tuples with fields:
//   <valuation, rank, sign, (..), oddity> and sign in {+1,-1}
function CreateGenusLabel(genus_sym)
    rk := Rank(genus_sym);
    sig := Signature(genus_sym);
    det := Abs(Determinant(genus_sym));

    primes := PrimeDivisors(2*det);

    // Jordan rank decompositions for primes with v_p(det) > 1
    local_symbols_filtered := [ SymbolTupleList(LocalSymbol(genus_sym, p))
                                : p in primes | Valuation(det, p) gt 1 ];
    max_vals := [ s[#s][1] : s in local_symbols_filtered ];
    rks := [ [ 0 : i in [1..max_val] ] : max_val in max_vals ];
    for i->s in local_symbols_filtered do
        for t in s do
            if t[1] gt 0 then
                // t[1] = valuation, t[2] = rank
                rks[i][t[1]] := t[2];
            end if;
        end for;
    end for;
    jordan_ranks := [ &cat [ EncodeRank(r) : r in rklist ] : rklist in rks ];

    // Local data bits (start with p = 2)
    s2 := LocalSymbol(genus_sym, 2);
    block_n := NumberOfBlocks(s2);
    train_ends := [ tr[#tr] : tr in Trains(s2) ];
    assert train_ends[#train_ends] eq block_n - 1;

    bits := [];

    // Compartments bitset over blocks 0..block_n-1
    comparts := &cat Compartments(s2);
    compart_symbol := &+ [ 2^e : e in comparts ];
    bits cat:= DigitsLSB(compart_symbol, block_n);

    // Oddities: 3 bits per compartment, packed little-endian by compartment index
    can_sym := CanonicalSymbol(s2);
    oddities := [ (&+ [ can_sym[t][5] : t in cmpart ]) mod 8 : cmpart in Compartments(s2) ];
    oddities_symbol := &+ [ o * 2^(3*(i-1)) : i->o in oddities ];
    bits cat:= DigitsLSB(oddities_symbol, 3 * #Compartments(s2));

    // Signs of trains at 2: store (1 - sign)/2
    signs2 := [ can_sym[Trains(s2)[i][1]][3] : i in [1..#Trains(s2)] ];
    bits cat:= [ (1 - s) div 2 : s in signs2 ];

    // For other primes dividing det: append signs of nonzero blocks
    assert primes[1] eq 2;
    for p in primes[2..#primes] do
        sp := LocalSymbol(genus_sym, p);
        tups := SymbolTupleList(sp);
        signs := [ t[3] : t in tups ];
        bits cat:= [ (1 - s) div 2 : s in signs ];
    end for;

    // Little-endian bits -> integer
    local_data := &+[ bits[i] * 2^(i-1) : i in [1..#bits] ];

    // Assemble label: r.s.d.j1.j2...jk.x
    comps := [ IntegerToString(rk),
               IntegerToString(sig),
               IntegerToString(det) ] cat
             jordan_ranks cat
             [ IntegerToString(local_data, 16) ];
    return Join(comps, ".");
end function;

// ---------------------------------------------------------------------------
// Inverse of CreateGenusLabel: build the Magma genus symbol (SymGen) from an
// LMFDB label.  This is a translation of the Python genus_symbol_from_label in
// genus.py, with two corrections to that reference:
//   (1) field 2 of the label is n_plus (not the signature), so we read it
//       directly instead of computing (rk + sig)/2 -- the Python version only
//       works for positive-definite genera because of this;
//   (2) Jordan-rank fields are present only for primes p with v_p(det) > 1, so
//       for primes with v_p(det) <= 1 we reconstruct the (determined) component
//       structure rather than consuming a field (the Python version misaligns
//       the fields when some prime has v_p(det) = 1).
// ---------------------------------------------------------------------------

// Inverse of EncodeRank: ASCII code of a base-62 digit (0-9 a-z A-Z) -> integer.
// (Magma's StringToCode returns the integer code of a single character.)
function DecodeRank(code)
    if code ge 48 and code le 57 then return code - 48;       // '0'..'9'
    elif code ge 97 and code le 122 then return code - 87;    // 'a'..'z' -> 10..35
    else return code - 29; end if;                            // 'A'..'Z' -> 36..61
end function;

// Least nonsquare unit mod an odd prime p, used to realise a Jordan block whose
// determinant has Kronecker symbol -1 (the label only records the square class).
function NonsquareUnit(p)
    g := GF(p);
    for d in [2..p-1] do
        if not IsSquare(g!d) then return d; end if;
    end for;
    return 1;
end function;

// Reconstruct the compartments and trains of the 2-adic symbol from the block
// valuations and the per-block "in a compartment" bits.  A direct port of the
// Python build_compartments_and_trains (block indices are 0-based throughout).
function BuildCompartmentsAndTrains(val2, compart_bits)
    num := #val2;
    compartments := [];  trains := [];
    in_comp := false;  train_start := 0;  compart_start := 0;  scale_diff := 0;
    for i in [0..num-1] do
        if i gt 0 then
            scale_diff := val2[i+1] - val2[i];
            if (scale_diff gt 2) and (i gt train_start) then
                Append(~trains, [train_start..i-1]);  train_start := i;
            end if;
        end if;
        if compart_bits[i+1] eq 1 then
            if in_comp then
                if (i gt 0) and (scale_diff gt 1) then
                    Append(~compartments, [compart_start..i-1]);  compart_start := i;
                end if;
            end if;
            if not in_comp then
                compart_start := i;  in_comp := true;
                if (i gt train_start) and (scale_diff gt 1) then
                    Append(~trains, [train_start..i-1]);  train_start := i;
                end if;
            end if;
        else
            if in_comp then
                in_comp := false;
                Append(~compartments, [compart_start..i]);
                if (i gt train_start) and (scale_diff eq 2) then
                    Append(~trains, [train_start..i-1]);  train_start := i;
                end if;
            else
                if i gt train_start then
                    Append(~trains, [train_start..i-1]);  train_start := i;
                end if;
            end if;
        end if;
    end for;
    if in_comp then Append(~compartments, [compart_start..num-1]); end if;
    Append(~trains, [train_start..num-1]);
    return compartments, trains;
end function;

intrinsic GenusSymbolFromLabel(label::MonStgElt) -> SymGen
{Create a genus symbol from an LMFDB label.}
    sl := Split(label, ".");
    rk := StringToInteger(sl[1]);
    nplus := StringToInteger(sl[2]);          // field 2 is n_plus
    nminus := rk - nplus;
    det := StringToInteger(sl[3]);
    primes := PrimeDivisors(2*det);

    // Jordan block (valuation, rank) data for each prime.  A jordan-rank field is
    // present only when v_p(det) > 1; otherwise the structure is determined.
    jidx := 0;  pvals := [];  pranks := [];
    for p in primes do
        vp := Valuation(det, p);
        if vp gt 1 then
            jidx +:= 1;
            jstr := sl[3 + jidx];
            rank_dec := [DecodeRank(StringToCode(Substring(jstr, k, 1))) : k in [1..#jstr]];
            rank_dec := [rk - &+rank_dec] cat rank_dec;     // prepend the valuation-0 block
            vals := [];  ranks := [];
            for v in [0..#rank_dec-1] do
                if rank_dec[v+1] gt 0 then
                    Append(~vals, v);  Append(~ranks, rank_dec[v+1]);
                end if;
            end for;
        elif vp eq 1 then
            vals := [0, 1];  ranks := [rk-1, 1];
        else
            vals := [0];  ranks := [rk];
        end if;
        Append(~pvals, vals);  Append(~pranks, ranks);
    end for;

    local_data := StringToInteger(sl[3 + jidx + 1], 16);    // the trailing hex field

    // --- prime 2: compartments, trains, oddities and train signs ---
    val2 := pvals[1];  rank2 := pranks[1];  nb := #val2;
    compart_bits := [ (local_data div 2^(i-1)) mod 2 : i in [1..nb] ];
    parities2 := compart_bits;
    comps, trains := BuildCompartmentsAndTrains(val2, compart_bits);
    local_data := local_data div 2^nb;
    ncomp := #comps;
    oddbits := [ (local_data div 2^(i-1)) mod 2 : i in [1..3*ncomp] ];
    odd_per_comp := [ &+[ oddbits[3*(j-1)+k+1]*2^k : k in [0..2] ] : j in [1..ncomp] ];
    local_data := local_data div 2^(3*ncomp);
    nt := #trains;
    train_sign_bits := [ (local_data div 2^(i-1)) mod 2 : i in [1..nt] ];
    local_data := local_data div 2^nt;

    dets2 := [ 1 : i in [1..nb] ];  oddities2 := [ 0 : i in [1..nb] ];
    for j in [1..ncomp] do oddities2[comps[j][1]+1] := odd_per_comp[j]; end for;
    for t in [1..nt] do
        dets2[trains[t][1]+1] := (train_sign_bits[t] eq 1) select 3 else 1;
    end for;

    symbs := [* LocalGenus(2, val2, rank2, dets2 : Parities := parities2, Oddities := oddities2) *];

    // --- odd primes: per-block determinant signs ---
    for jp in [2..#primes] do
        p := primes[jp];  vals := pvals[jp];  ranks := pranks[jp];  n := #vals;
        sign_bits := [ (local_data div 2^(i-1)) mod 2 : i in [1..n] ];
        local_data := local_data div 2^n;
        dets := [ sign_bits[i] eq 0 select 1 else NonsquareUnit(p) : i in [1..n] ];
        Append(~symbs, LocalGenus(p, vals, ranks, dets));
    end for;

    return Genus(nplus, nminus, det, [ s : s in symbs ]);
end intrinsic;
