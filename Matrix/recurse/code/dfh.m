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

/* T is composition tree; index identifies leaf of tree; construct 
   preimages in root of tree of user-generators of leaf */

PreimagesOfCompositionFactor := function (T, index)
   G := GroupOfNode (T[index]);
   gens := G`UserGenerators;
   return [PreimageInRoot (T, index, g): g in gens];
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

/* 
W := PreimagesOfFactors (T);
Y := [[G`SLPGroupHom (w): w in x]: x in W];
d := Degree (G); F := BaseRing (G);
CS := [sub < GL(d, F) | &cat[Y[i]: i in [#Y..j by -1]]>: j in [#Y..1 by -1]];

index := 2;
repeat 
   g := Random (G);
until g in CS[index] and not (g in CS[index - 1]);

flag, w, id := SolveWord (T, T[1], g);
*/
