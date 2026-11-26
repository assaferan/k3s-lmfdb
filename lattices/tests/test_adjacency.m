// NeighbourAdjacencyMatrix (adjacency.m): where Magma's AdjacencyMatrix is right
// (even genera, odd primes) the two must agree; for odd genera at p = 2, where
// Magma returns the zero matrix (Magma-Maths/Magma#496), the matrix is checked
// against a hand count and against the Hecke relation
//     A[i,j] * #Aut(L_i) = A[j,i] * #Aut(L_j),
// which holds for any p-neighbour graph of a genus, since both sides count the
// pairs (L_i, L_j) at distance one weighted by automorphisms.
AttachSpec("lattices.spec");
load "tests/assertions.m";
results := NewResults();
SetSeed(1);

cartan := func<s | LatticeWithGram(CartanMatrix(s))>;

function reps_of(L)
    return [LatticeWithGram(LLLGram(ChangeRing(GramMatrix(M), Integers()))) : M in GenusRepresentatives(L)];
end function;

// Order-independent fingerprint of an adjacency matrix: the order of the
// representatives depends on GenusRepresentatives and on the Magma version.
fingerprint := func<A | <CharacteristicPolynomial(A), Sort(Eltseq(A))>>;

function hecke_relation(A, reps)
    au := [#AutomorphismGroup(L) : L in reps];
    return forall{<i, j> : i, j in [1..#reps] | A[i, j] * au[i] eq A[j, i] * au[j]};
end function;

// even genera and odd primes, where Magma's AdjacencyMatrix is right: its
// matrices, from V2.30-1.  (CI runs V2.29-4, where AdjacencyMatrix itself fails
// at p = 2 with "Invalid attribute 'IsNatural'", so they are not recomputed.)
expected := [* <"E8+A1", DirectSum(cartan("E8"), cartan("A1")),
                 [* <2, [255]>, <3, [3280]> *]>,
               <"E7+A2", DirectSum(cartan("E7"), cartan("A2")),
                 [* <2, [252, 120, 3, 135]>, <3, [3304, 2240, 56, 1120]>, <5, [95760, 75840, 1896, 21816]> *]>,
               <"Z^9", StandardLattice(9),
                 [* <3, [3024, 1920, 256, 1360]>, <5, [88440, 69120, 9216, 28536]> *]>,
               <"Z^8+[3]", DirectSum(StandardLattice(8), LatticeWithGram(Matrix(Integers(), 1, 1, [3]))),
                 [* <3, [1568, 432, 0, 1792, 2920, 2240, 0, 8, 1120]>,
                    <5, [34680, 15120, 17280, 62720, 82320, 60480, 256, 216, 19896]> *]> *];
for c in expected do
    reps := reps_of(c[2]);
    h := #reps;
    for e in c[3] do
        A := NeighbourAdjacencyMatrix(reps, e[1]);
        AssertTrue(~results, fingerprint(A) eq fingerprint(Matrix(Integers(), h, h, e[2])),
              Sprintf("%o, p = %o: AdjacencyMatrix's matrix up to the order of the classes", c[1], e[1]));
    end for;
end for;

// odd genera at p = 2.  Z^9: the lines <v> with v.v = 0 mod 4 are the 126 + 9 = 135
// of weight 4 and 8, each with two neighbours, so 270 neighbours per class.
reps := [StandardLattice(9), DirectSum(cartan("E8"), StandardLattice(1))];
A := NeighbourAdjacencyMatrix(reps, 2);
AssertTrue(~results, A eq Matrix(Integers(), 2, 2, [252, 135, 18, 135]), "Z^9, p = 2: matrix");
AssertTrue(~results, hecke_relation(A, reps), "Z^9, p = 2: Hecke relation");

// odd genera of even det, where Magma's Neighbor refuses p = 2
for c in [* <"Z^8+[2]", DirectSum(StandardLattice(8), LatticeWithGram(Matrix(Integers(), 1, 1, [2])))>,
            <"Z^6+A3", DirectSum(StandardLattice(6), cartan("A3"))> *] do
    reps := reps_of(c[2]);
    A := NeighbourAdjacencyMatrix(reps, 2);
    AssertTrue(~results, not IsZero(A), Sprintf("%o, p = 2: nonzero", c[1]));
    AssertTrue(~results, hecke_relation(A, reps), Sprintf("%o, p = 2: Hecke relation", c[1]));
end for;

// scaling the genus does not change the matrix
reps := reps_of(DirectSum(cartan("E8"), cartan("A1")));
AssertTrue(~results, NeighbourAdjacencyMatrix([ScaledLattice(L, 3) : L in reps], 3) eq NeighbourAdjacencyMatrix(reps, 3),
      "E8+A1 scaled by 3, p = 3: same matrix");

Report(~results, "test_adjacency");
