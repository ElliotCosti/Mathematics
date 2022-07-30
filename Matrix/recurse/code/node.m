forward RandomElementsSatisfyLeaf;

/* do the test elements associated with G 
   preserve the Aschbacher category? */

ElementsSatisfyAschbacher := function (G, TestElements) 

   if not assigned G`ActionType then 
      error "2 ElementsSatisfyAschbacher: Problem in ActionType";
   end if;

   if G`ActionType eq "reducible" then  
      return ElementsActReducibly (G, TestElements);
   elif G`ActionType eq "absolutereducible" then 
      return ElementsActAbsolutelyReducibly (G, TestElements);
   elif G`ActionType eq "imprimitive" then 
      return ElementsActImprimitively (G, TestElements);
   elif G`ActionType eq "semilinear" then 
      return ElementsActSemilinearly (G, TestElements);
   elif G`ActionType eq "tensor" then 
      return ElementsActAsTensor (G, TestElements);
   elif G`ActionType eq "tensorinduced" then 
      return ElementsActAsTensorInduced (G, TestElements);
   elif G`ActionType eq "smaller" then 
      return ElementsOverSmallerField (G, TestElements);
   elif G`ActionType eq "extra" then 
      return ElementsActAsExtraSpecial (G, TestElements);
   elif G`ActionType eq "unipotent" then 
      return true;
   elif G`ActionType eq "determinant" then 
      return true;
   else
      error "1 ElementsSatisfyAschbacher: Problem in ActionType";
   end if;
end function;

/* construct subtree of node */

ProcessNode := function (node, A: KnownLeaf := false, 
                         KernelOnly := false, KernelRank := 12);

   vprint User4: "node ", node`identifier, 
                 " is group of order ", #node`group;

   identifier := node`identifier;

   G := GroupOfNode (node);

   if Type (G) eq GrpMat and KnownLeaf eq false then 
      flag, I := ConstructAction (G);
      node`group := G;
   elif Type (G) eq GrpPC or Type (G) eq GrpPerm or Type (G) eq GrpAb then 
      flag := false;
      I := sub <G |>;
   end if;
   
   if KnownLeaf then flag := false; I := G; end if;

   vprint User1: "leaf? ", not flag;
   leaf, node := NodeIsLeaf (node, flag, I);
   A[node`identifier] := node;

  // if leaf eq true then return A; end if;

   if leaf eq true then
if not IsLeftChild (node, A) then 
      if #A eq 1 then vprint User1: "Tree with 1 node"; newflag := true; else 
      newflag := RandomElementsSatisfyLeaf (node); end if;
      if newflag eq false then 
         A, id := Crisis (node, A); 
         if Type (A) eq BoolElt then vprint User1: "1 CRISIS"; return false; end if;
         vprint User1: "Now back from Crisis";
         vprint User1: "id is ", id;
         A := $$ (A[id], A); 
      else 
         A[node`identifier] := node;
      end if;
end if;
      return A;
   end if;

   d := Degree (G);
   F := BaseRing (G);

   node := A[identifier];
   G := GroupOfNode (node);

   if not ElementsSatisfyAschbacher (G, G`RandomElements) then 
      vprintf User1: "ProcessNode: Aschbacher test failed -- crisis\n"; 
      "Aschbacher failure -- call crisis for node ", node`identifier;
      A, id := Crisis (node, A); 
      if Type (A) eq BoolElt then vprint User1: "2 CRISIS"; return false; end if;
      vprint User1: "Return from crisis: start at node ", id;
      return $$ (A[id], A); 
   end if;

   node := A[identifier];
   G := GroupOfNode (node);

   /* set up right node, treat scalar separately */
   U := UserGenerators (G);
   alpha := U[1]; Remove (~U, 1);
   I`UserGenerators := [ImageOfScalar (G, alpha)] cat 
                       [ConstructImage (G, u): u in U];
   I`SLPGroup := G`SLPGroup;
    
   if Type (I) eq GrpMat then 
      I`SLPGroupHom := MyHom (I, I`SLPGroup, I`UserGenerators);
   elif Type (I) eq GrpPC then 
      I`SLPGroupHom :=  hom <I`SLPGroup -> I | I`UserGenerators>;
   elif Type (I) eq GrpPerm then 
      I`SLPGroupHom :=  hom <I`SLPGroup -> I | I`UserGenerators>;
   elif Type (I) eq GrpAb then 
      I`SLPGroupHom :=  hom <I`SLPGroup -> I | I`UserGenerators>;
   else
      error "Error in ProcessNode: Type of right node";
   end if;
    
   R := G`RandomElements;
   I`RandomElements := [ConstructImage (G, r): r in R];
   I`CentraliserTrees := [ ];

   CreateNode (I, "", node`identifier, #A + 1, ~RightChild);
   Append (~A, RightChild);
   node`right := RightChild`identifier;
   A[node`identifier] := node;

   vprint User2: "Just set up right node", node`right, 
                 " having parent ", node`identifier;

   A := $$ (RightChild, A);
   if Type (A) eq BoolElt then vprint User1: "3 CRISIS"; return false; end if;
 
   /* this node may have disappeared or been updated */
   if node`identifier gt #A then return A; end if;
 
   node := A[node`identifier];
 
   if IsNodeProcessed (node, A) then
      return A;
   end if;

   RightChild := A[RightChildOfNode (A[node`identifier])];

   node := A[node`identifier];
   G := GroupOfNode (node);

   /* construct generators for left node */
   LIMIT := KernelRank;
   // LIMIT := 6;
   U := UserGenerators (G);
   gens, words := InitialiseKernel (G, U[1]);
   vprint User4: "node ", node`identifier, " has order ", #node`group;
   vprint User1: "now construct kernel of node ", node`identifier;
   for i in [1..LIMIT] do

      g, gword := RandomWord (G);
      image := ConstructImage (G, g);

      flag, word := SolveWord (A, RightChild, image);
      vprint User2: 
          "Generators of kernel: flag returned by SolveWord: ", flag;
      if not (flag cmpeq true) then 
         "word is ", word; 
         error "PROBLEM in ProcessNode"; 
      end if;
      im, iword := EvaluateWord (G, word);

      k := g * im^-1;

      if k ne Id (G) then 
         kword := gword * iword^-1;  
         Append (~gens, k);
         Append (~words, kword);
      end if;
   end for;

   if #gens gt 0 then  
      MyParent := Parent (Rep (gens));
      K := sub < GL(Degree (MyParent), BaseRing (MyParent)) | gens >;
   else 
      K := sub <GL (d, F) | gens>;
   end if;

   vprint User4: "Node ", node`identifier, " has order ", #node`group;
   vprint User1: "Generators of kernel constructed for node ", 
                  node`identifier;
   vprint User4: "Kernel constructed for node ", 
                  node`identifier, "has order", #K;

   K`UserGenerators := gens;
   K`UserWords := words;
   B := SLPGroup (#gens);
   K`SLPGroup := B;
   K`SLPGroupHom := MyHom (K, B, gens);
   K`CentraliserTrees := [ ];

   myrandom := [];
   R := G`RandomElements;
   for i in [1..#R] do
      image := ConstructImage (G, R[i]);
      flag, word := SolveWord (A, RightChild, image);
      vprint User2: "Random element processing for kernel: ";
      vprint User2: "right child flag returned by SolveWord is ", flag;
      if flag cmpeq false then 
         vprint User1: "Kernel Random element right flag -- crisis";
         A, id := Crisis (node, A); 
         if Type (A) eq BoolElt then vprint User1: "4 CRISIS"; return false; end if;
         vprint User1: "Return from crisis: start at node ", id;
         return $$ (A[id], A); 
      end if;
      im, iword := EvaluateWord (G, word);
      k := R[i] * im^-1;
      Append (~myrandom, k);
   end for;

   K`RandomElements := myrandom;
   
   /* set up left node */
   CreateNode (K, "nonroot", node`identifier, #A + 1, ~LeftChild);
   Append (~A, LeftChild);
   node`left := LeftChild`identifier;
   A[node`identifier] := node;

   vprint User2: "Just set up left node", node`left, " having parent ", 
                 node`identifier;

   if KernelOnly then return A; end if;

   A := $$ (LeftChild, A);
   if Type (A) eq BoolElt then vprint User1: "5 CRISIS"; return false; end if;

   return A;
    
end function;

/* initialise root of composition tree */

InitialiseRoot := function (G : RandomElts := []) 

   if RandomElts cmpeq [] then 
      NSTEPS := 100; NRANDOM := 100;
      P := RandomProcess (G : Scramble := NSTEPS);
      R := [Random (P): i in [1..NRANDOM]];
      G`RandomElements := R;

   if assigned G`UserGenerators then 
      U := G`UserGenerators;
   else 
      U := [Identity (G)] cat [G.i : i in [1..Ngens (G)]];
   end if;
   
   m := #U;

   G`UserGenerators := U;

   if not assigned G`SLPGroup then 
   B := SLPGroup (m);
   gamma := hom < B -> G | U >;
   G`SLPGroup := B;
   G`SLPGroupHom := gamma;
   G`UserWords := [B.i : i in [1..m]];
   G`CentraliserTrees := [ ];
   end if;

   else 
      G`RandomElements := RandomElts;
   end if;

   CreateNode (G, "root", 0, 1, ~node);  
   A := [node];

   return A;
end function;

/* construct composition tree for G */

CompositionTree := function (G: KnownLeaf := false, KernelOnly := false, KernelRank := 20, RandomElts := [])
   A := InitialiseRoot (G: RandomElts := RandomElts);
   node := A[1];
   B := ProcessNode (node, A: KnownLeaf := KnownLeaf, 
               KernelOnly := KernelOnly, KernelRank := KernelRank);
   return B;
end function;

/* write random element of G as word in 
   user-generators, using the composition tree A */

TestElements := function (G, A)
   h := G`SLPGroupHom;
   for g in G`RandomElements do 
      f, w := SolveWord (A, A[1], g);
      assert f eq true;
      assert h (w) eq g;
   end for;
   return true;
end function;

RandomElementToWord := function (G, A)
   g := Random (G);
   h := G`SLPGroupHom;
   f, w := SolveWord (A, A[1], g);
   return h (w) eq g, w, g;
end function;

/* check that the tree is valid */

CheckTree := function (B)

   for i in [1..#B] do
      if HasChildren (B[i], B) then
	 l := B[LeftChildOfNode (B[i])];        
	 r := B[RightChildOfNode (B[i])];        
	 assert #B[i]`group eq #l`group * #r`group;
      end if;
   end for;

   return true;
end function;

/* list composition factors */

TreeFactors := function (T)

   if Type (T) ne SeqEnum then error "Requires composition tree"; end if;
   order := 1;
   L := [* *];
   for i in [1..#T] do
      if HasChildren (T[i], T) eq false and 
         Order (T[i]`group) gt 1 then 
         L[#L + 1] := T[i];
	 order *:= #T[i]`group;
      end if;	  
   end for;
   scalars := &*[Order (L[i]`group`UserGenerators[1]): i in [1..#L]];
   return L, order, scalars;
end function;
