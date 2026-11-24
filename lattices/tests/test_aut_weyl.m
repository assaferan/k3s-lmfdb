// AutomorphismGroupWeyl (aut_weyl.m) and the AutomorphismGroupFaster path that
// uses it: on each lattice, in a scrambled basis, the group must preserve the
// Gram matrix and have the order of Magma's AutomorphismGroup.  The cases cover
// norm-2 roots only (simply laced), norm-1 and norm-2 roots together (Z^n, type
// B), a lattice without roots (Magma fallback), decomposable lattices, and an
// indecomposable lattice whose root system does not span it.
AttachSpec("lattices.spec");
load "tests/assertions.m";
results := NewResults();
SetSeed(1);

cartan := func<s | LatticeWithGram(CartanMatrix(s))>;
function scramble(L)
    U := RandomSLnZ(Rank(L), 3, 6);
    return LatticeWithGram(U * GramMatrix(L) * Transpose(U));
end function;

// A2 scaled by 2 has minimum 4, so no roots.
rootless := LatticeWithGram(Matrix(Integers(), 2, 2, [4, 2, 2, 4]));
// indecomposable, det 11, two pairs of roots that do not span it
odd4 := LatticeWithGram(Matrix(Integers(), 4, 4, [2,1,0,1, 1,2,0,0, 0,0,2,1, 1,0,1,3]));

cases := [* <"E8", cartan("E8")>, <"D4+A2", DirectSum(cartan("D4"), cartan("A2"))>,
            <"Z^5", StandardLattice(5)>, <"Z^2+A3", DirectSum(StandardLattice(2), cartan("A3"))>,
            <"E7+E7", DirectSum(cartan("E7"), cartan("E7"))>, <"rootless", rootless>,
            <"odd4", odd4> *];

for c in cases do
    name := c[1]; L := scramble(c[2]); g := GramMatrix(L);
    n := #AutomorphismGroup(LatticeWithGram(g));
    W := AutomorphismGroupWeyl(LatticeWithGram(g));
    AssertTrue(~results, forall{x : x in Generators(W) | x * g * Transpose(x) eq g},
               name cat ": AutomorphismGroupWeyl preserves the Gram matrix");
    AssertEqual(~results, #W, n, name cat ": AutomorphismGroupWeyl order");
    F := AutomorphismGroupFaster(LatticeWithGram(g));
    AssertTrue(~results, forall{x : x in Generators(F) | x * g * Transpose(x) eq g},
               name cat ": AutomorphismGroupFaster preserves the Gram matrix");
    AssertEqual(~results, #F, n, name cat ": AutomorphismGroupFaster order");
    // the order is the order of the generated group, not just the stored value
    AssertEqual(~results, #sub<GL(Rank(L), Integers()) | Generators(W)>, n,
                name cat ": AutomorphismGroupWeyl generators generate the full group");
end for;

Report(~results, "test_aut_weyl");
