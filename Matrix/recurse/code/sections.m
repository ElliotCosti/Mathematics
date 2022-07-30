/* extract from g rows & columns listed in index */

ExtractAction := function (g, index)
   E := [];
   F := BaseRing (Parent (g));
   if Type (index) eq SetEnum then 
      index := Sort (SetToSequence (index)); 
   end if;
   for i in index do 
      for j in index do
         // E cat:= (ExtractBlock (g, i, j, 1, 1));
         Append (~E, g[i][j]);
      end for;
   end for;
   return GL(#index, F) ! (E);
end function;

/* extract chosen composition factor */

ExtractFactor := function (G, index)
   U := UserGenerators (G);
   if Type (index) eq SetEnum then 
      index := Sort (SetToSequence (index)); 
   end if;
   X := [ExtractAction (U[i], index): i in [1..#U]];
   H := sub < GL(#index, BaseRing (G)) | X >;
   H`UserGenerators := X;
   if assigned G`UserGenerators then
      assert #H`UserGenerators eq #G`UserGenerators;
   end if;
   return H;
end function;

/* return action of matrix g on composition factors of G */

MatrixBlocks := function (G, g)

   CF := G`CompositionFactors;
   COB := G`ChangeOfBasis;
   F := BaseRing (G);
   d := Degree (G);
   e := [* *];
   I := COB * g * COB^-1;
   offset := 0;
   for i in [1..#CF] do 
      k := Dimension (CF[i]);
      e[i] := GL (k, F) ! ExtractBlock (I, offset + 1, offset + 1, k, k);
      offset +:= k;
   end for;
   return e;
end function;

/* actions on module composition factors of G */

Sections := function (G)
   M := GModule (G);
   F := BaseRing (G);
   d := Degree (G);
   CS, CF, COB := CompositionSeries (M);
   G`CompositionFactors := CF;
   G`ChangeOfBasis := GL (d, F) ! COB;
   offset := 0;
   U := UserGenerators (G);
   E := [* *];
   for j in [1..#U] do 
      E[j] := MatrixBlocks (G, U[j]);
   end for; 
   section := [* *];
   for i in [1..#CF] do 
      k := Dimension (CF[i]);
      gens := [E[j][i]: j in [1..#U]];
      section[i] := sub < GL(k, F) | gens>;
      section[i]`UserGenerators := gens;
   end for;
   return section;
end function;

/* identify groups in L */

IdentifySections := function (L)  
   sl := [* *];
   for i in [1..#L] do
      C := L[i];
      F := BaseRing (C);
      dets := {Determinant (g): g in Generators (C)};
      if #dets gt 0 then 
         o := LCM ([Order (x): x in dets]);
      else 
         o := 1;
      end if;
      if Degree (C) gt 1 then 
         flag := RecognizeClassical (C);
      else 
         flag := false;
      end if;
      sl[i] := <Degree (C), flag, o>;
   end for;
   return sl;
end function;
