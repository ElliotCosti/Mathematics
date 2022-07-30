forward SetupMatrixLeaf, SLPImage;

/* return generators for composition series of leaf,
   which has subgroup generated by a at bottom */

C9Leaf := function (G, a)
  
  N := SolubleRadical(G);
  RQ, phi := RadicalQuotient(G);
  S := Socle(RQ);
  SQ, psi := SocleQuotient(RQ);
  PSQ, SQtoPC := PCGroup(SQ);
  CPSQ := CompositionSeries(PSQ);
  CTopG := [[(((CPSQ[i].j)@@SQtoPC)@@psi)@@phi : j in [1..Ngens(CPSQ[i])]] : 
            i in [1..#CPSQ-1]];
  CS := [[(S.i)@@phi : i in [1..Ngens(S)]]];
  // assert a in N;
  A := sub<N | a>;
  PN, NtoPC := PCGroup(N);
  PA := A@NtoPC;
  PQ, quot := quo<PN|PA>;
  CPQ := CompositionSeries(PQ);
  CBotG := [[((CPQ[i].j)@@quot)@@NtoPC : j in [1..Ngens(CPQ[i])]]: 
             i in [1..(#CPQ - 1)]];
  if IsTrivial (A) eq false then CBotG cat:= [[A.1]]; end if;
  if IsTrivial (RQ) then 
     return Reverse((CBotG));
  else 
     return Reverse((CTopG cat CS cat CBotG));
  end if;
end function;
  
/* return composition series for leaf, where
   last term is that generated by a */

SubsForC9Leaf := function (G, a)
  // assert a in G;
  gens := C9Leaf(G, a);
  subs := [sub < G | >] cat [sub<G | &cat[gens[i] : i in [1..j]]> : j in [1..#gens]];
//  subs := [sub < G | >] cat [sub<G | &cat[gens[i] : i in [2..j]]> : j in [1..#gens]];
  return subs;
end function;

/* set up composition series and other machinery for matrix group */

CompositeMatrixLeaf := function (G)
   a := UserGenerators (G)[1];
   S := SubsForC9Leaf (G, a);

   G`SLPGroupHom := MyHom (G, G`SLPGroup, G`UserGenerators);
   SetupMatrixLeaf (G);

   T := [* G *];

   for i in [#S-1..1 by -1] do
      H := S[i];
      H`UserGenerators := UserGenerators (H);
      H`SLPGroup := SLPGroup(#H`UserGenerators);
      H`SLPGroupHom := MyHom (H, H`SLPGroup, H`UserGenerators);
      SetupMatrixLeaf (H);
      Append (~T, H);
   end for;
   return T;
end function;

/* T is composition series for composite matrix
   leaf group G; identify term of composition series
   containing g; return true, SLP for g in user-defined
   generators of that term, and index of term */

ImageCompositeMatrixLeaf := function (G, T, g)

   if IsIdentity (g) then
      return true, Identity (T[1]`SLPGroup), #T;
   end if;

   for i in [1..#T - 1] do
      if g in T[i] and not (g in T[i + 1]) then 
         flag, w := SLPImage (T[i], g);
         assert flag;
         U := UserGenerators (T[i]);
         S := T[1]`SLPGroup;
         UW := [];
         for j in [1..#U] do
            flag, uw := SLPImage (T[1], U[j]);
            assert flag;
            UW[j] := uw;
         end for;
         tau := hom <Parent (w) -> S | UW >;
         return true, tau (w), i;
     end if;
   end for;
   return false, 0, 0;
end function;
         
/* set up composition series and other machinery for permutation group */

CompositePermLeaf := function (G)
   a := UserGenerators (G)[1];
   S := SubsForC9Leaf (G, a);

   delta := InverseWordMap (G);
   G`InverseWordMap := delta;

   T := [* G *];

   for i in [#S-1..1 by -1] do
      H := S[i];
      delta := InverseWordMap (H);
      H`InverseWordMap := delta;
      Append (~T, H);
   end for;
   return T;
end function;

/* T is composition series for composite permutation
   leaf group G; identify term of composition series
   containing g; return true, SLP for g in user-defined
   generators of that term, and index of term */

ImageCompositePermLeaf := function (G, T, g)

   if IsIdentity (g) then
      return true, Identity (T[1]`SLPGroup), #T;
   end if;

   for i in [1..#T - 1] do
      if g in T[i] and not (g in T[i + 1]) then 
         "found index ", i;
         delta := T[i]`InverseWordMap;
         return true, g @ delta, i;
     end if;
   end for;
   return false, 0, 0;
   return false, _, _;
end function;

/* set up composition series and other machinery for pc-group */

CompositePCLeaf := function (G)
   gamma, C := CosetAction (G, sub <G | >);
   U := UserGenerators (G);

   s := sub <C | [gamma (u): u in U]>;
   delta := InverseWordMap (s);

   a := UserGenerators (s)[1];
   S := SubsForC9Leaf (s, a);

   delta := InverseWordMap (s);
   G`InverseWordMap := gamma * delta;
   // G`UserGenerators := [s.i @@ gamma : i in [1..Ngens (s)]];

   T := [* G *];

   for i in [#S-1..1 by -1] do
      delta := InverseWordMap (S[i]);
      H := S[i] @@ gamma;
      H`InverseWordMap := gamma * delta;
      H`UserGenerators := [S[i].j @@ gamma : j in [1..Ngens (S[i])]];
      Append (~T, H);
   end for;
   return T;
end function;

/* T is composition series for composite pc
   leaf group G; identify term of composition series
   containing g; return true, SLP for g in user-defined
   generators of that term, and index of term */

ImageCompositePCLeaf := function (G, T, g)

   if IsIdentity (g) then
      return true, Identity (T[1]`SLPGroup), #T;
   end if;

   for i in [1..#T - 1] do
      if g in T[i] and not (g in T[i + 1]) then 
         "found index ", i;
         delta := T[i]`InverseWordMap;
         return true, g @ delta, i;
     end if;
   end for;
   return false, 0, 0;
   return false, _, _;
end function;

/* set up composition series and other machinery for abelian group */

CompositeAbelianLeaf := function (G)
   gamma, C := CosetAction (G, sub <G | >);
   U := UserGenerators (G);

   s := sub <C | [gamma (u): u in U]>;
   delta := InverseWordMap (s);

   a := UserGenerators (s)[1];
   S := SubsForC9Leaf (s, a);

   delta := InverseWordMap (s);
   G`InverseWordMap := gamma * delta;
   // G`UserGenerators := [s.i @@ gamma : i in [1..Ngens (s)]];

   T := [* G *];

   for i in [#S-1..1 by -1] do
      delta := InverseWordMap (S[i]);
      H := S[i] @@ gamma;
      H`InverseWordMap := gamma * delta;
      H`UserGenerators := [S[i].j @@ gamma : j in [1..Ngens (S[i])]];
      Append (~T, H);
   end for;
   return T;
end function;

/* T is composition series for composite abelian
   leaf group G; identify term of composition series
   containing g; return true, SLP for g in user-defined
   generators of that term, and index of term */

ImageCompositeAbelianLeaf := function (G, T, g)

   if IsIdentity (g) then
      return true, Identity (T[1]`SLPGroup), #T;
   end if;

   for i in [1..#T - 1] do
      if g in T[i] and not (g in T[i + 1]) then 
         "found index ", i;
         delta := T[i]`InverseWordMap;
         return true, g @ delta, i;
     end if;
   end for;
   return false, 0, 0;
end function;

/* T composition series for G;  which term contains g? */

IdentityIndex := function (T, g)
   if IsIdentity (g) then return #T; end if;

   for i in [1..#T - 1] do
      if g in T[i] and not (g in T[i + 1]) then 
         return i;
      end if;
   end for;

   error "Error in IdentifyIndex -- should not be here";

end function;

RefinedImageCompositeLeaf := function (G, g)
   if not (g in G) then return false, _, _; end if;
   T := G`CompSeries;
   if Type (G) eq GrpMat then
      flag, w, index := ImageCompositeMatrixLeaf (G, T, g);
   elif Type (G) eq GrpPerm then
      flag, w, index := ImageCompositePermLeaf (G, T, g);
   elif Type (G) eq GrpAb then
      flag, w, index := ImageCompositeAbelianLeaf (G, T, g);
   elif Type (G) eq GrpPC then
      flag, w, index := ImageCompositePCLeaf (G, T, g);
   end if;
   return flag, w, index;
   error "Should not be here in RefinedImage";
end function;
