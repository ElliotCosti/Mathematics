/* action of g on chosen composition factor */

ImageOfReducibleElement := function (G, g)
   index := G`CompositionFactor;
   b := MatrixBlocks (G, g);
   return b[index];
end function;

/* choose composition factor of smallest dimension
   on which G has non-trivial action */

ChooseSection := function (G)
   S := Sections (G);
   smallest := Degree (G) + 1; index := 1;
   for i in [1..#S] do
      deg := Degree (S[i]);
      if Ngens (S[i]) gt 0 and deg lt smallest then
         smallest := deg;
         index := i;
      end if;
   end for;
   return index, S;
end function;

/* set up reducible action for G */

ReducibleAction := function (G)

   index, S := ChooseSection (G);
   G`CompositionFactor := index;
   return true, S[index];

end function;

/* do TestElements preserve module structure? */

ElementsActReducibly := function (G, TestElements)
 
   M := GModule (G);
   CS := CompositionSeries (M);
   F := BaseRing (G);
   d := Degree (G);
   V := VectorSpace (F, d);

   for sub in CS do 
      W := sub <V | [Eltseq (M!x): x in Basis (sub)]>;
      if exists {x : x in TestElements | W^x ne W} then
         return false;  
      end if;                            
   end for;
   return true;
end function;
