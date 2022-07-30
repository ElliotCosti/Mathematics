/* A is lower-triangular matrix; extract the off-diagonal in 
   position index where main diagonal has index position 0 */

OffDiagonal := function (A, index)

   n := Nrows (A);
   if index ge n then return false; end if;
   return [A[i][i - index] : i in [index + 1..n]];

end function;

ExpandImage := function (image)

   Z := Integers ();
   I := Eltseq (image);
   I := &cat[Eltseq (x) : x in I];
   I := [Z ! x : x in I];
   return I;
end function;

/* set up necessary machinery to take homomorphic image of 
   unipotent group to subspace of vector space 
   spanned by off-diagonal elements of some particular
   index [= elementary abelian group] */ 

UnipotentAction := function (G)

   M := GModule (G);
   CS, CF, t := CompositionSeries (M);
   F := BaseRing (G);
   d := Degree (G);

   U := UserGenerators (G);
   S := [GL(d, F) ! (t * U[i] * t^-1): i in [1..#U]];
   j := 0;
   repeat 
      j +:= 1;
      V := VectorSpace (F, d - j);
      images := [V!OffDiagonal (S[i], j): i in [1..#U]];
      depth := Maximum ([Depth (s): s in images]);
   until j ge d or depth gt 0; 

   if j eq d then return true; end if;

   q := #F;
   p := Characteristic (F);
   flag, e := IsPowerOf (q, p); r := Degree (Rep (images));
   E := AbelianGroup (GrpPC, [p : i in [1..r * e]]);

   Z := Integers ();
   J := [];
   for i in [1..#images] do 
      I := Eltseq (images[i]);
      I := &cat[Eltseq (x) : x in I];
      I := [Z ! x : x in I];
      J[i] := E!I;
   end for;
     
   I := sub <E | J>;
   I`UserGenerators := [E!j: j in J];
   G`ChangeOfBasis := t;
   G`UnipotentDepth := j;
   G`UnipotentImage := I;
   G`ParentUnipotentImage := E;

   return I;

end function;

ImageOfUnipotentElement := function (G, g)
    
   E := G`ParentUnipotentImage;
   t := G`ChangeOfBasis;
   j := G`UnipotentDepth;
   d := Degree (G);
   F := BaseRing (G);
   V := VectorSpace (F, d - j);

   /* since we don't know g is an element of unipotent group G,
      image of g need not be in G`UnipotentImage, only
      in parent E of this image */ 

   return (E ! ExpandImage(OffDiagonal (t * g * t^-1, j)));

end function;

/* is G unipotent? */

IsUnipotent := function (G)

   M := GModule (G);
   CS, CF := CompositionSeries (M);
   if exists {i : i in [1..#CF] | Dimension (CF[i]) gt 1} then 
      return false;
   end if;
   for i in [1..#CF] do
      if exists {j : j in [1..Ngens (G)] | 
            not IsIdentity (ActionGenerator (CF[i], j))} then
         return false;
      end if;
   end for; 

   return true;

end function;
