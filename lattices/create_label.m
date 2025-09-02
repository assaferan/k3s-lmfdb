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
