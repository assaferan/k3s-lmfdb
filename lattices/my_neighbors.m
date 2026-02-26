Z := Integers();
import !"/Lattice/Lat/neighbors.m":BinaryNeighbors,SetDepth,TwoNeighbors,Adjust,IsNonsingularVector,AdjoinNeighbor;
// Attach("aut-char.mag");
// import "aut-char.mag":AutomorphismGroupFaster;

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
  vprint Genus: "Number of orbits:", #O;
  TA := 0;
  for o in O do
    v := L ! o[1].1;
    if Norm(v) mod 4 eq 0 and not IsZero(v) then
      // latter check to catch a bug in LineOrbit
      // now that we have better isomorphism testing, this one is a
      // serious waste of time.
      // AdjoinNeighbor(~TA, ~Lambda, Neighbor(L,v,2), dep);
      try
        nb := Neighbor(L,v,2);
        // I believe the issue here is only that sometimes we go from odd to
        // even and it isn't in the same genus
        if Genus(nb) eq Genus(L) then
          vprint Genus,2: "adding new lattice";
          Append(~Lambda,nb);
        end if;
      catch e; end try;
      
      B := [ b : b in Basis(L) | (v,b) mod 2 eq 1 ];
      if #B gt 0 then
        v +:= 2*B[1];
        // AdjoinNeighbor(~TA, ~Lambda, Neighbor(L,v,2), dep);
        try
          nb := Neighbor(L,v,2);
          if Genus(nb) eq Genus(L) then
            vprint Genus,2: "adding new lattice";
            Append(~Lambda,nb);
          end if;
        catch e;
        end try;
      end if;
    end if;
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
