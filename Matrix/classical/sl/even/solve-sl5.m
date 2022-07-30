forward SolveSmaller;
forward ChosenElements;

/* 
   I   X  Y   *  I     X      U            I   0   * 
       B  Z            I    B^-1*Z     =       B   0   
          I                   I                    I
             
     R       *        S              =        T

   We can construct R; we want to construct T as word;
   to do this we construct S and take product R * S to obtain T
*/

Degree5LinearProblem := function (G, C, m: ProcessA := true)

   d := Degree (G);
   K := BaseRing (G);

   A := C;
   B := C;

   b := d - 2 * m;
   repeat 
      y, w := PullbackInvolution (G, B, [2..d - m]: SmallerCorank := true);
      // assert G`SLPGroupHom (w) eq y;

      /* construct element of form I  *  * by squaring y 
                                   0  I  *              
                                   0  0  I               */
      y := y^(2); w := w^2;
      X := ExtractBlock (y, 1, m + 1, m, b);
      Y := ExtractBlock (y, m + 1, d - m + 1, d - 2 * m, m);
   until Rank (X) gt 0 and Rank (Y) gt 0;

   /* size of B block */
   b := d - 2 * m;
   X := ExtractBlock (y, 1, m + 1, m, b);
   Y := ExtractBlock (y, m + 1, d - m + 1, d - 2 * m, m);

   // assert G`SLPGroupHom (w) eq y;

   assert Rank (X) eq m;
     
   k := Degree (K);
   p := Characteristic (K);
   F := GF(p);

   V := VectorSpace (F, 2 * m * (d - 2 * m) * k);

   /* find spanning basis for V consisting of conjugates of y */
   M, I, wI := ObtainBasis (G, B, B, y, V, m);

   U := UserGenerators (B);
   W := UserWords (B);

   b := d - 2 * m;
   New := []; Word := [];

   for i in [1..#U] do 
      hold := U[i];
      whold := W[i];

      bb := ExtractBlock (hold, m + 1, m + 1, d - 2 * m,d - 2 * m);
      u := V! ((&cat[Eltseq (x): x in 
                &cat[Eltseq (ExtractBlock (hold, 1, m + 1, m, b))]]) cat 
     (&cat[Eltseq (x): x in 
 &cat[Eltseq (bb^-1 * ExtractBlock (hold, m + 1, d - m + 1, d - 2 * m, m))]]));
      flag, coords := IsConsistent (M, u);

      coords := [Integers ()! x : x in Eltseq (coords)];
      product := &*[(y^I[i])^coords[i]: i in [1..#coords]];
      wproduct := &*[(w^wI[i])^coords[i]: i in [1..#coords]];
      // assert G`SLPGroupHom (wproduct) eq product;

      /* now hold * product has both above-diagonal blocks cleared out */

      New[i] := hold * product;
      Word[i] := whold * wproduct;
   end for;

   return New, Word;
end function;

/* construct Steinberg basis for G = SL (5, q);
   do this by first solving an SL4, then an SL3 which
   is centraliser of involution in G; we can now combine
   cycles for each to produce n-cycle */

SolveSL5 := function (G)
   // InitialiseGroup (G);
   F := BaseRing (G);
   d := Degree (G);
   ranks := [4];

   /* construct SL4 as subgroup */
   H, rank, COB := ConstructSmallerSL (G, ranks);
   K := ExtractGroup (H, [1..4]);
   A, WA, CA := SolveSL4 (K);
   WA  := ImagesOfWords(K, H, WA);
   WA := [PullbackWord (G, H, w): w in WA];
   
   /* now centraliser of involution 1 1   0  
                                    0 1   0 
                                          I  */
   x := A[3];
   M := MatrixAlgebra (F, d);
   B := Identity (M);
   InsertBlock (~B, CA, 1, 1);
   cb := B * COB;

   I := Identity (M);
   InsertBlock (~I, x, 1, 1);
   I := GL(d, F) ! (cb^-1 * I * cb);
   wI := WA[3];

   /* centraliser contains SL3 */

   C := CentraliserOfInvolution (G, I, wI);
   C := ApplyCOB (C, cb);

//  [ cb * G`SLPGroupHom (C`UserWords[i]) * cb^-1 eq 
//  C`UserGenerators[i]: i in [1..Ngens (C) + 1]];

   RowBaseChange := function (G)
      d := Degree (G);
      F := BaseRing (G);
      V := VectorSpace (F, d);
      B := [V.1, V.3, V.4, V.5, V.2];
      CB := GL(d, F) ! &cat[Eltseq (v): v in B];
      return CB;
   end function;

   D := MyDerivedSubgroupWithWords (C);
   W := D`UserWords;
   W := [PullbackWord (G, C, w): w in W];
   D`UserWords := W;

   CR := RowBaseChange (G);
   D := ApplyCOB (D, CR);
// [CR * cb * G`SLPGroupHom (D`UserWords[i]) * cb^-1 * CR^-1 eq 
// D`UserGenerators[i]: i in [1..Ngens (C) + 1]];

   /* now clean up D to obtain SL3 as subgroup of G */
   gens, W := Degree5LinearProblem (G, D, 1);
   gens := [x^2: x in gens];
   W := [w^2: w in W];

// [CR * cb * G`SLPGroupHom (W[i]) * cb^-1 * CR^-1 eq gens[i]: i in [1..#W]];

   /* SL3 as subgroup of SL5 */ 
   D := sub <GL (d, F) | gens>;
   _ := InitialiseGroup (D : generators := gens, scalars := false);

   /* solve SL3 */
   K := ExtractGroup (D, [2..4]);
   K`UserWords := W;
   B, WB, CB := SolveSmaller (K);
   WB := [PullbackWord (G, K, w): w in WB];

   /* we now know a = (1, 4, 3, 2) and b = (3, 5, 4) */
   a := Identity (M);
   InsertBlock (~a, A[2], 1, 1);
   wa := WA[2];

   b := Identity (M);
   InsertBlock (~b, B[2], 3, 3);
   wb := WB[2];

   /* form 5-cycle */
   cycle := (a * b)^4 * b;
   wcycle := (wa * wb)^4 * wb;

   A := ChosenElements (G: Words := false);
   WA[2] := wcycle;

   return A, WA, cb;

end function;
