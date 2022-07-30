/* define corank (g) = Rank (g - g^0);

   given an involution g of corank m, produce a change 
   of basis so that g has shape 
        I 0 I1
        0 I 0 
        0 0 I
   where I1 is identity matrix of rank m */

InvolutionBaseChange := function (G, g)
   d := Degree (G);
   F := BaseRing (G);
   V := VectorSpace (F, d);
   MA := MatrixAlgebra (F, d);
   g := MA!g;
   gm1 := g - Id(MA);
   I := sub<V | [gm1[i] : i in [1..d]]>;
   N := Nullspace (gm1);
   B := ExtendBasis (Basis (I), N);
   B := ExtendBasis (B, V);
   Reverse (~B);
   b := Dimension (I);
   K := sub < V | I, N>;
   offset := Dimension (K);
   for i in [1..b] do
      B[offset + i] := B[i] * gm1;
   end for;
   B := MA ! &cat[Eltseq (B[i]): i in [1..d]];
   return GL(d, F) ! B;
end function;
