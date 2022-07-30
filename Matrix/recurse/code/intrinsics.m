/* get a random element of G and return it both as a
   straight-line program and as an element */

intrinsic RandomWord (G:: Grp) -> GrpMatElt, GrpSLPElt
{construct a random element of G and return it both as a
 element and as straight-line program}

   if not assigned G`SLPGroup and not assigned G`SLPGroupHom then
      "Input group must have associated SLPGroup and homomorphism";
      return false, _;
   end if;

   B := G`SLPGroup;

   if not assigned B`RandomProcess then
      P := RandomProcess (B: Scramble := 100);
      B`RandomProcess := P;
   else
      P := B`RandomProcess;
   end if;

   w := Random (P);
   gamma := G`SLPGroupHom;
   g := gamma (w);
   return g, w;

end intrinsic;

/* 
intrinsic ElementOfOrder (G:: Grp, RequiredOrder, 
          Limit:: RngIntElt: Word := true, Fct := Order) -> GrpMatElt
{Fct can be Order or ProjectiveOrder; search at most Limit times for 
 element of (projective) order RequiredOrder; if found return element
 and possibly word, else return false}

   if Type (G) ne GrpMat then Fct := Order; end if;

   if not Word then 
      P := RandomProcess (G); 
   end if;

   if Type (RequiredOrder) eq RngIntElt then
      RequiredOrder := {RequiredOrder};
   end if;

   NmrTries := Limit;
   repeat
      if Word then 
         g, wg := RandomWord (G);
         if Type (g) eq BoolElt then return false, _; end if;
      else 
         g := Random (P);
      end if;
      o := Fct (g: Proof := false);
      NmrTries -:= 1;
      rem := exists (x) {x : x in RequiredOrder | (o mod x eq 0)};
   until rem or (NmrTries eq 0);

   if rem then o := o div x; 
      if Word then return g^o, wg^o; else return g^o, _; end if; 
   end if;

   return false, _;

end intrinsic;
*/

/* try to prove that G is perfect by proving that its generators
   are in G'; we do this by showing that the orders of the
   generators are 1 modulo G'

   algorithm is Monte-Carlo; if "true" is returned, then G is perfect;
   if "false" is returned, then G might still be perfect;

   basis of algorithm outlined in Leedham-Green and O'Brien;
   J. Algebra 253, 2002, 14-30 */

/* 
intrinsic IsProbablyPerfect (G :: GrpMat : NumberRandom := 100) -> BoolElt
{this Monte-Carlo algorithm tries to prove that G is perfect by
 establishing that its generators are in G'; if "true" is returned, then
 G is perfect; if "false" is returned, then G might still be perfect}

   K := sub<G | [ (G.i, G.j): i in [1..Ngens (G)], j in [1..Ngens (G)]]>;
   Z := Integers ();
   trial := [1..Ngens (G)];
   O := [{Z|} : i in [1..Ngens (G)]];
   for j in [1..NumberRandom] do
      k := NormalSubgroupRandomElement (G, K);
      for i in trial do
         o := Order (G.i * k: Proof := false);
         Include (~O[i], o);
      end for;
      trial := [i : i in [1..Ngens (G)] | Gcd (O[i]) ne 1];
      // "Trial is now", trial;
      if #trial eq 0 then return true; end if;
   end for;

   return false;
end intrinsic;

intrinsic ImprimitiveBasis (G::GrpMat) -> GrpMatElt 
{Change-of-basis which exhibits block structure for imprimitive group}
   blocks := Blocks (G);
   d := Degree (G);
   F := BaseRing (G);
   B := &cat[&cat[Eltseq (blocks[i].j): j in [1..Dimension (blocks[1])]]: 
      i in [1..#blocks]];
   return GL(d, F) ! B;
end intrinsic;

intrinsic IsCentral (H :: Grp, h:: GrpElt) -> BoolElt
{If h central in H, return true, else false}
   return forall {i : i in [1..Ngens (H)] | (h, H.i) eq Id (H)};
end intrinsic;

intrinsic IsIdentity (x :: AlgMatElt) -> BoolElt
{Is x identity matrix?}
  return x^0 eq x;
end intrinsic;    
*/
