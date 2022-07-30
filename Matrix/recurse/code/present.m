/* write down a presentation for a leaf on the user generators */

PresentationForLeaf := function (node, A)

   K := GroupOfNode (node);
   U := K`UserGenerators;

   u := #U;
   F := SLPGroup (u);
   if #U eq 0 then F`Relations := []; return F; end if;

   PK, phiK := FPGroup (K);
   n := Ngens (PK);
   E := [phiK (PK.i): i in [1..n]];

   /* generators of PK as words in U */
   W := [];
   for i in [1..#E] do 
      flag, w := SolveWord (A, node, E[i]); 
      if flag cmpeq false then error "Presentation problem"; end if;
      B := Parent (w);
      f := hom <B -> F | [F.(i): i in [1..u]]>;
      Append (~W, f (w));
   end for; 

   /* relations of K */
   f := hom <PK -> F | W>;
   R := Relations (PK); 
   R := [f (r): r in R];                                                       
   /* now relations between user generators */
   id := Id (F);
   Rels := [];
   for i in [1..#U] do 
       flag, w := SolveWord (A, node, U[i]); 
       if flag cmpeq false then error "Presentation problem"; end if;
       B := Parent (w);
       f := hom <B -> F | [F.i: i in [1..u]]>;
       r := F.i = f(w);
       // prevent Id (F) = Id (F) relations 
       if LHS (r) ne RHS (r) then 
          Append (~Rels, r);
       end if;
   end for; 

   F`Relations := R cat Rels;
   "Number of relations in leaf is ", #F`Relations;
   return F;

end function;

MyRelations := function (P)

   if Type (P) cmpeq GrpSLP and assigned P`Relations then
      return P`Relations;
   else
      error "Input not correct";
   end if;      
end function;

/* write down a presentation for a node on 
   its user-supplied generating set */

PresentationForNode := function (node, A)

   if IsLeaf (node) then
      return PresentationForLeaf (node, A);
   end if;

   G := GroupOfNode (node);
   L := A[LeftChildOfNode (node)];
   K := GroupOfNode (L);
   R := A[RightChildOfNode (node)];
   I := GroupOfNode (R);

   PK := $$ (L, A);
   PI := $$ (R, A);

   F := G`SLPGroup;
   id := Identity (F);

   /* defining generators of kernel K expressed as words in 
      generators of G */
   words := K`UserWords;

   /* conjugates of kernel generators expressed as words in 
      generators of K */

   conjugates := [];
   UG := UserGenerators (G);
   UK := UserGenerators (K);
   for i in [1..#UG] do 
      for j in [1..#UK] do 
	 // y := RewriteElement (G, UG[i]);
         z := UK[j]^UG[i];
         flag, w := SolveWord (A, L, z);
         if flag eq false then error "kernel is not normal"; end if;
         f := hom <Parent (w) -> F | words>;
         reln := words[j]^F.i = f (w); 
         if LHS (reln) ne RHS (reln) then 
            Append (~conjugates, reln); 
         end if;
      end for;
   end for;
   "Number of conjugates is ", #conjugates;
    
   /* relations of K */
   RelsK := MyRelations (PK);
   f := hom <PK -> F | words>;
   RelsK := [f (r): r in RelsK];
   "Number of relations of K is ", #RelsK;

   /* finally relators of I lifted to G, evaluated in K and 
      solved there */

   gamma := hom <PI -> F | [F.i : i in [1..Ngens (PI)]]>;
   // tau := hom <PI -> G | UserGenerators (G)>;
   tau := MyHom (G, PI, UserGenerators (G));

   R := MyRelations (PI);
   R := [LHS (r) * RHS (r)^-1: r in R];
   E := [tau (x): x in R ];

   imagerels := [];
   for i in [1..#E] do 
      // "now process relator ", i;
      flag, w := SolveWord (A, L, E[i]);
      if flag eq false then error "kernel is not normal"; end if;
      f := hom <Parent (w) -> F | words>;
      reln := gamma (R[i]) = f (w); 
      if LHS (reln) ne RHS (reln) then 
         Append (~imagerels, reln);
      end if;
   end for;

   F`Relations := conjugates cat RelsK cat imagerels; 
   return F;

end function;

/* verify that G satisfies the relations of P */

VerifyPresentation := function (G, P)
   U := UserGenerators (G);
   tau := hom <P -> G | U>;
   R := MyRelations (P);
   R := [LHS (x) * RHS (x)^-1 : x in R];
   return forall {r: r in R | tau (r) eq Id (G)};
end function;
