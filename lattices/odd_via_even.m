// The genus of an odd lattice through its even sublattice.
//
// For an odd lattice L of even determinant the p-neighbour walk cannot use p = 2
// and runs at p = 3, where newNeighbours computes the orbits of Aut(L) on the
// (3^n - 1)/2 lines of L/3L.  At rank 16 that is 21.5 million lines and 60-90 s
// for every lattice the walk expands, so a rank-16 walk hardly gets started
// within the fill timeout.
//
// The even sublattice L0 = {x in L : x.x even} has index 2 in L, and every N in
// the genus of L is M + Zv for its own even sublattice M, which lies in the genus
// of L0 (determined by the genus of L), and a class v of order 2 in M^#/M with
// v.v odd.  An isometry N -> N' maps M onto M' and v onto v', so the classes of
// the genus of L are in bijection with the pairs (M, Aut(M)-orbit of such v) with
// M + Zv in the genus of L, M running over the classes of the genus of L0.  L0 is
// even, so its genus is walked at p = 2 (2^n - 1 lines), and no isometry tests
// are needed between the odd classes.

// One lattice per class of the genus of L among the overlattices M + Zv of M.
function odd_overlattices(M, GL)
    D := Dual(M : Rescale := false);
    A, q := D / M;
    cands := [a : a in A | Order(a) eq 2];
    vs := [a @@ q : a in cands];
    odd := [i : i in [1 .. #vs] | IsIntegral(Norm(vs[i])) and IsOdd(Integers() ! Norm(vs[i]))];
    if #odd eq 0 then return []; end if;
    // M has the standard basis of its ambient space, so Aut(M) acts on ambient
    // coordinates, and hence on D and on A.
    gens := [ChangeRing(Matrix(g), Rationals()) : g in Generators(AutomorphismGroupFaster(M))];
    seen := { A | };
    out := [];
    for i in odd do
        if cands[i] in seen then continue; end if;
        orb := { cands[i] };
        todo := [ cands[i] ];
        while #todo gt 0 do
            a := todo[#todo];
            Prune(~todo);
            v := ChangeRing(Vector(Eltseq(a @@ q)), Rationals());
            for g in gens do
                b := q(D ! (v * g));
                if b notin orb then
                    Include(~orb, b);
                    Append(~todo, b);
                end if;
            end for;
        end while;
        seen join:= orb;
        N := sub<D | [D ! b : b in Basis(M)] cat [vs[i]]>;
        N := LatticeWithGram(ChangeRing(GramMatrix(N), Integers()));
        if Genus(N) eq GL then Append(~out, N); end if;
    end for;
    return out;
end function;

intrinsic GenusRepresentativesOddViaEven(L::Lat : even_reps := []) -> SeqEnum, BoolElt
{Representatives of the classes of the genus of the odd positive definite lattice L,
from the classes of the genus of its even sublattice (computed with
GenusRepresentativesFaster, i.e. walked at p = 2, unless given as even_reps).  The
second value is true when the representatives account for the whole mass of the
genus.}
    require IsPositiveDefinite(GramMatrix(L)) : "L must be positive definite";
    require not IsEven(L) : "L must be odd";
    if #even_reps eq 0 then
        L0 := LatticeWithGram(GramMatrix(EvenSublattice(L)));
        even_reps := [x : x in GenusRepresentativesFaster(L0)];
    end if;
    GL := Genus(L);
    reps := [];
    for M in even_reps do
        reps cat:= odd_overlattices(LatticeWithGram(GramMatrix(M)), GL);
    end for;
    m := &+[Rationals() | 1 / #AutomorphismGroupFaster(N) : N in reps];
    return reps, m eq Mass(L);
end intrinsic;
