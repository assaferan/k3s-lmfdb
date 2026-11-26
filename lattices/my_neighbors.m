Z := Integers();
import !"/Lattice/Lat/neighbors.m":BinaryNeighbors,SetDepth,TwoNeighbors,Adjust,IsNonsingularVector,AdjoinNeighbor;
// Attach("aut-char.mag");
// import "aut-char.mag":AutomorphismGroupFaster;

// The norm mod 8 of a characteristic vector w of the integral Gram matrix G
// of odd determinant, i.e. (x, w) = (x, x) mod 2 for all x.  Any two choices
// differ by 2y with (w, y) = (y, y) mod 2, so the norm is well defined mod 8; it
// is the oddity of the unimodular Z_2-lattice with Gram matrix G.
function char_norm_mod8(G)
  G := ChangeRing(G, Z);
  n := Nrows(G);
  w := Solution(ChangeRing(G, GF(2)), Vector(GF(2), [G[i,i] : i in [1..n]]));
  wz := ChangeRing(w, Z);
  return InnerProduct(wz * G, wz) mod 8;
end function;

// The 2-neighbour {x in L : (x, w) even} + Z w/2 of the integral lattice L,
// for w in L with w.w = 0 mod 4 and (w, L) not in 2Z.
function two_neighbour(L, w)
  G := ChangeRing(GramMatrix(L), Z);
  n := Nrows(G);
  c := Vector(Z, Coordinates(w));
  K := Kernel(Matrix(GF(2), n, 1, Eltseq(c * G)));
  Lw := Matrix(Z, [Eltseq(ChangeRing(b, Z)) : b in Basis(K)] cat
                  [Eltseq(2 * x) : x in Rows(IdentityMatrix(Z, n))]);
  H := HermiteForm(VerticalJoin(2 * Lw, Matrix(Z, 1, n, Eltseq(c))));
  B := ChangeRing(Submatrix(H, 1, 1, n, n), Rationals()) / 2;
  return LatticeWithGram(ChangeRing(B * ChangeRing(G, Rationals()) * Transpose(B), Z));
end function;

// dep now ignored; retained for backward compatibility
function newTwoNeighbors(L, dep)
  Lambda := [ Parent(L) | ]; 
  /// L := CoordinateLattice(LLL(L));
  llmat,lllto := LLLGram(GramMatrix(L));
  lll := LatticeWithGram(llmat);
  if assigned L`AutomorphismGroup then
    lll`AutomorphismGroup := L`AutomorphismGroup^(GL(Rank(L),Z)!lllto^-1);
    assert forall{x: x in Generators(lll`AutomorphismGroup)|x*GramMatrix(lll)*Transpose(x) eq GramMatrix(lll)};
  end if;
  L := lll;
  
  G := ChangeRing( AutomorphismGroupFaster(L:orth_bd := 10), GF(2));
  O := LineOrbits(G);
  vprint Genus,2: "Number of orbits:", #O;
  TA := 0;
  // A 2-neighbour nb of L has the same determinant, and nb and L agree at every
  // odd prime p (both contain L meet nb with index 2), so nb is in the genus of
  // L exactly when its 2-adic genus is that of L.  Comparing Genus(nb) with
  // Genus(L) diagonalised both at every prime dividing 2 det, for every
  // neighbour, and was most of a rank-16 walk.
  // When det L is odd, L is unimodular at 2, and a unimodular Z_2-lattice is
  // determined by its rank, determinant, parity and oddity.  The oddity is the
  // norm mod 8 of a characteristic vector (van der Blij), so the test needs one
  // linear solve mod 2 instead of a 2-adic Jordan decomposition (on rank-16
  // genera of odd determinant LocalGenus was 55-58% of the walk).
  if IsOdd(Determinant(L)) then
    oddity := char_norm_mod8(GramMatrix(L));
    same_genus := func<nb | exists{i : i in [1..Nrows(G)] | IsOdd(G[i,i])} and char_norm_mod8(G) eq oddity
                            where G is ChangeRing(GramMatrix(nb), Z)>;
  else
    gL2 := LocalGenus(L, 2);
    same_genus := func<nb | LocalGenus(nb, 2) eq gL2>;
  end if;
  // Each line <v> with v.v = 0 mod 4 and v not in the radical of L/2L has two
  // neighbours, {x in L : (x, v) even} + Z w/2 for w = v and w = v + 2b with
  // (v, b) odd.  They are built directly: Magma's Neighbor refuses p = 2 on odd
  // lattices of even determinant ("singular point of quadratic form"), and the
  // try/catch that used to wrap it dropped every such neighbour.
  for o in O do
    v := L ! o[1].1;
    if Norm(v) mod 4 ne 0 or IsZero(v) then continue; end if;
    B := [ b : b in Basis(L) | (v,b) mod 2 eq 1 ];
    if #B eq 0 then continue; end if;   // v in the radical of L/2L
    for w in [v, v + 2*B[1]] do
      nb := two_neighbour(L, w);
      if same_genus(nb) then
        vprint Genus,2: "adding new lattice";
        Append(~Lambda,nb);
      end if;
    end for;
  end for;
  return Lambda;
end function;

// Depth now ignored; retained for backward compatibility
intrinsic newNeighbours(L::Lat, p::RngIntElt : 
                        Depth := -1, Bound := 2^32) -> SeqEnum
   {The immediate p-neighbors of L.}

   vprint CanonicalForm,3: "entering newNeighbours";
   require IsExact(L) : "Argument 1 must be an exact lattice";
   require IsPrime(p) : "Argument 2 is not a prime";
   p *:= Sign(p);

   if Rank(L) eq 2 then
     return BinaryNeighbors(L,p);
   end if;

   c := Content(L);
   if c ne 1 then
     Lc := LatticeWithGram((1/c)*GramMatrix(L));
     if assigned L`AutomorphismGroup then
       Lc`AutomorphismGroup := L`AutomorphismGroup;
     end if;
     L := Lc;
   end if;
   // require Type(Depth) eq RngIntElt and Depth ge -1:
   //  "Parameter 'Depth' should be a non-negative integer.";
   dep := SetDepth(Rank(L),Depth);
     
   if p^Rank(L) gt Bound then
     require false : 
         "Error: Requires computation of orbits of", p^Rank(L), "points\n"
         cat "Increase Bound parameter to proceed at your own risk.";
   elif p^Rank(L) gt (Bound div 2^8) then
     vprint Genus : "Warning: may be slow and memory intensive.";
   end if;

   if p eq 2 and IsOdd(L) then
     Lambda := newTwoNeighbors(L, dep);
   else
     Lambda := [ Parent(L) | ]; 
     lll,lllto := LLL(L);
     lll := LatticeWithGram(GramMatrix(lll));
     if assigned L`AutomorphismGroup then
       lll`AutomorphismGroup := L`AutomorphismGroup^(GL(Rank(L),Z)!lllto^-1);
     end if;
     L := lll;
     if not assigned L`AutomorphismGroup then
       vprint CanonicalForm,3: "computing automorphism group";
     end if;
     G := ChangeRing( AutomorphismGroupFaster(L: orth_bd := 10), GF(p));
     vprint CanonicalForm,3: "computing line orbits";
     O := LineOrbits(G);
     good := true;
     if (Determinant(L) mod p) eq 0 then
       good := false;
     end if; 
     for o in O do
       v := Adjust(L!o[1].1,p);
       if not IsZero(v) then
         if good or IsNonsingularVector(v,p) then
           vprint CanonicalForm,4: "found new neighbour";
           Append(~Lambda, Neighbor(L, v, p));
         end if;   
       end if;
     end for;
   end if;
   if c eq 1 then
     return Lambda;
   else
     return [ ScaledLattice(N,c) : N in Lambda ];
   end if;
end intrinsic;

newNeighbors := newNeighbours;
