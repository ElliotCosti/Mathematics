/* g is an element of T[index]; pull back its SLP to root of T */
   
PreimageInRoot := function (T, index, g)
   PullbackToParent := function (node, w)
      p  := ParentOfNode (node);
      PN := T[p];
      P := PN`group;
      S := P`SLPGroup;

      if IsRightChild (node, T) then
         theta := hom <Parent(w) -> S | [S.i:  i in [1..Ngens (S)]]>; 
     else
        theta := hom <Parent (w) -> S | GroupOfNode (node)`UserWords>;
     end if;
     w := theta (w);
     return w;
   end function;

   node := T[index];
   flag, w := SolveWord (T, node, g);
   while IsRootNode (node) eq false do 
      w := PullbackToParent (node, w);
      node := T[ParentOfNode (node)];
   end while;

   return w;
   
end function;

/* T is composition tree; index identifies leaf of tree; 
   construct preimages in root of tree of user-generators 
   of composition series of leaf */

PreimagesOfCompositionFactor := function (T, index)
   G := GroupOfNode (T[index]);
   CS := G`CompSeries;
   /* only pull back terms which don't correspond to the scalar matrix */ 
   if IsIdentity(G`UserGenerators[1]) then 
      last := #CS - 1; 
   else 
      last := #CS - 2; 
   end if;
   L := [* *];
   // for i in [1..#CS - 1] do
   for i in [1..last] do
      // gens := CS[i]`UserGenerators;
      gens := UserGenerators (CS[i]);
      new := [x : x in gens | not (x in CS[i + 1])];
      P := [PreimageInRoot (T, index, g): g in gens];
      Append (~L, <P, index, i>);
   end for;
   return L;
end function;

/* T is composition tree; return preimages in 
   root of each composition factor */

PreimagesOfFactors := function (T)
   L := [* *];
   for i in [1..#T] do
      if IsLeaf (T[i]) then 
         G := GroupOfNode (T[i]);
         if IsTrivial (G) eq false then
            W := PreimagesOfCompositionFactor (T, i);
            Append (~L, W);
         end if;
      end if;
   end for;
   return L;
end function;

/* A is composite leaf node; express g as a word in user generators 
   of appropriate subgroup of composition series */

WriteAsSLP := function (A, node, g: Factor := <[0,0], g>)

   if Factor[1] ne [0,0] then factor := Factor; else factor := <[0,0], g>; end if;

   G := GroupOfNode (node);

   if not IsLeaf (node) then 
      vprint User2: "Here test of Aschbacher category";
      if ElementsSatisfyAschbacher (G, [g]) eq false then 
         "Element doesn't satisfy Aschbacher class";
         return false, node`identifier, _; 
      end if;
   end if;

   if IsLeaf (node) then 
      A[node`identifier] := node;
      if IsRybaGroup (G) then 
         vprint User1: "Call Centraliser of Involution procedure";
         flag, word := Ryba (G, g);
      elif IsSL2Group (G) cmpeq true then
         // vprint User1: "Call SL2 procedure";
         flag, word := MySL2ElementToWord (G, g);
      else 
         /* the first computation writes g in terms of 
            user generators for index-th term of composition series of G;
            the second writes G in terms of generators of G;
            in general, second may be done by writing
            user generators of comp series subgroup in terms of 
            those of G; however currently all handled trivially
            within magma */

         flag, word, index := RefinedImageCompositeLeaf (G, g);
         flag, word := SLPImage (G, g);
      end if;
      if flag cmpeq false then 
         return false, _, _;
      else 
         if Factor[1] eq [0,0] and not IsIdentity (g) then 
            return true, word, <[node`identifier, index], g>;
         else 
            return true, word, Factor;
         end if;
      end if;
   end if;

   if RightChildOfNode (node) cmpeq false then 
      return "unknown", "";
   else 
      I := A[RightChildOfNode (node)];
   end if;

   /* solve for the right child */
   image := ConstructImage (G, g);
   flag, iword, identifier := $$ (A, I, image: Factor := factor);

   /* record first composition factor where image is non-trivial */
   if assigned identifier then 
      if factor[1] eq [0,0] then 
         factor := identifier;
      end if;
   end if;

   if flag cmpeq false or flag cmpeq "unknown" then 
      return flag, _, _;
   end if;

   /* now consider left child */
   if LeftChildOfNode (node) cmpeq false then
      return "unknown", "", _;
   else 
      K := A[LeftChildOfNode (node)];
   end if;

   im, iword := EvaluateWord (G, iword); 

   k := g * im^-1;

   flag, word2, Factor := $$ (A, K, k: Factor := factor);
   if flag cmpeq false or flag cmpeq "unknown" then 
      return flag, _, _;
   end if;

   /* rewrite word2, an element of kernel, as word in 
      generators of G */
   P := G`SLPGroup;
   theta := hom <Parent (word2) -> P | GroupOfNode (K)`UserWords>;
   return true, theta (word2) * iword, Factor;

end function;
