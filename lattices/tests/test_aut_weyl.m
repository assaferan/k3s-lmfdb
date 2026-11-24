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

// IsIsometricWeyl: scrambled copies are isometric; E8+E8 and the even
// unimodular D16+ both have 480 roots but are not isometric; Z^4 + A2 against
// D4 + Z^2 has the same rank but not the same roots; a rootless pair.
// D16+ = D16 + Z h, h = (1/2, ..., 1/2), inside Q^16 with the standard form
Q := Rationals();
B := [Vector(Q, [j eq i select 1 else (j eq i+1 select -1 else 0) : j in [1..16]]) : i in [1..15]]
     cat [Vector(Q, [j ge 15 select 1 else 0 : j in [1..16]]), Vector(Q, [1/2 : j in [1..16]])];
M := Matrix(B); Hm := ChangeRing(HermiteForm(Matrix(Integers(), 2 * M)), Q) / 2;
Bas := Matrix([Hm[i] : i in [1..16]]);
D16p := LatticeWithGram(ChangeRing(LLLGram(Bas * Transpose(Bas)), Integers()));
AssertTrue(~results, Determinant(D16p) eq 1 and IsEven(D16p) and #ShortVectors(D16p, 2) eq 240, "D16+ is even unimodular with 480 roots");
E8E8 := DirectSum(cartan("E8"), cartan("E8"));
pairs := [* <"E8+E8 vs scrambled", E8E8, scramble(E8E8), true>,
            <"D4+A2 vs scrambled", DirectSum(cartan("D4"), cartan("A2")),
                scramble(DirectSum(cartan("D4"), cartan("A2"))), true>,
            <"odd4 vs scrambled", odd4, scramble(odd4), true>,
            <"rootless vs scrambled", rootless, scramble(rootless), true>,
            <"E8+E8 vs D16+ (480 roots each)", E8E8, D16p, false>,
            <"Z^4+A2 vs D4+Z^2", DirectSum(StandardLattice(4), cartan("A2")),
                DirectSum(cartan("D4"), StandardLattice(2)), false> *];
for c in pairs do
    AssertEqual(~results, IsIsometricWeyl(c[2], c[3]), c[4], "IsIsometricWeyl: " cat c[1]);
end for;

Report(~results, "test_aut_weyl");
