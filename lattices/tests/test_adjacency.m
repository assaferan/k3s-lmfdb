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

function magma_adj(reps, p)
    G := Genus(reps[1]);
    G`Representatives := reps; G`IsNatural := true;
    return AdjacencyMatrix(G, p);
end function;

function hecke_relation(A, reps)
    au := [#AutomorphismGroup(L) : L in reps];
    return forall{<i, j> : i, j in [1..#reps] | A[i, j] * au[i] eq A[j, i] * au[j]};
end function;

// even genera and odd primes: agree with Magma
for c in [* <"E8+A1", DirectSum(cartan("E8"), cartan("A1")), [2, 3]>,
            <"E7+A2", DirectSum(cartan("E7"), cartan("A2")), [2, 3, 5]>,
            <"Z^9", StandardLattice(9), [3, 5]>,
            <"Z^8+[3]", DirectSum(StandardLattice(8), LatticeWithGram(Matrix(Integers(), 1, 1, [3]))), [3, 5]> *] do
    reps := reps_of(c[2]);
    for p in c[3] do
        AssertTrue(~results, NeighbourAdjacencyMatrix(reps, p) eq magma_adj(reps, p),
              Sprintf("%o, p = %o: agrees with AdjacencyMatrix", c[1], p));
    end for;
end for;

// odd genera at p = 2.  Z^9: the lines <v> with v.v = 0 mod 4 are the 126 + 9 = 135
// of weight 4 and 8, each with two neighbours, so 270 neighbours per class.
reps := [StandardLattice(9), DirectSum(cartan("E8"), StandardLattice(1))];
A := NeighbourAdjacencyMatrix(reps, 2);
AssertTrue(~results, IsZero(magma_adj(reps, 2)), "Z^9, p = 2: Magma's AdjacencyMatrix is zero (Magma-Maths/Magma#496)");
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
