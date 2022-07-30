/* rearrange rows of matrices */

ChangeBasis2 := function (G)
   d := Degree (G);
   F := BaseRing (G);
   V := VectorSpace (F, d);
   B := [V.2, V.3, V.1, V.4];
   CB := GL(d, F) ! &cat[Eltseq (v): v in B];
   return CB;
end function;

/* G is SL4; g is involution having shape 
           I  I
           0  I
   construct its centraliser and hence find another involution of corank 2; 
   both centralisers generate group T having form
           A   * 
           0   C
   now find in T the glue element 
                     0 1 0 0 
                     1 0 0 0
                     0 0 1 0
                     0 0 0 1
*/
   
FindGlueSL4 := function (G, g, w)
   d := Degree (G);
   F := BaseRing (G);
   C := CentraliserOfInvolution (G, g, w: N := 20, Nmr := 200);
   
   /* produce element h of form I J ; 0 I 
      where J is non-scalar */
   repeat 
      h, wh := PullbackInvolution (G, C, [1..2]);
      h := h^2; wh := wh^2;
      b := ExtractBlock (h, 1,3,2,2);
      found := IsScalar (b) eq false  and Rank (b) eq 2;
      "Found a good element? ", found;
   until found;

   assert Order (h) eq 2;
   
   C2 := CentraliserOfInvolution (G, h, wh: N := 10, Nmr := 100);

   T := sub < GL(d, F) | C, C2>;

   U := UserGenerators (C) cat UserGenerators (C2); 
   W := UserWords (C) cat UserWords (C2);
   _ := InitialiseGroup (T: generators := U, scalars:=false);
   T`UserWords := W;
   
   return LinearProblem (G, T);
  
end function;

/* given involution 
   1 0  0 0 
   1 1  0 0
   0 0  1 1
   0 0  0 1

   apply base change to obtain 
       1 0 1 0 
       0 1 0 1 
       0 0 1 0 
       0 0 0 1        

   we now find glue element in SL4
        0 1  0 0
        1 0  0 0
        0 0  1 0  
        0 0  0 1
   and undo base change to obtain our desired glue 
        1 0 0 0
        0 0 1 0 
        0 1 0 0
        0 0 0 1   
*/

GlueSL4 := function (G, g, wg)
   CB := ChangeBasis2 (G);
   H := ApplyCOB (G, CB);
   h := CB * g * CB^-1;
   a, wa := FindGlueSL4 (H, h, wg);
   wa := ImagesOfWords (G, H, [wa])[1];
   a := CB^-1 * a * CB;
   return a, wa;
end function;

PullbackElement := function (G, X, AX, x: ParentWord := true)
   F := BaseRing (G);
   flag, winv := MySL2ElementToWord (AX, x);
   winv := ImagesOfWords(AX, X, [winv]);
   winv := winv[1];
   inv := X`SLPGroupHom (winv);
   if ParentWord then winv := PullbackWord (G, X, winv); end if;
   return inv, winv;
end function;

/* g is involution; write it as 
              I I
              0 I
   construct its centraliser; obtain another involution
   of corank 2 and its centraliser;  the group spanned 
   by the two centralisers is
             A * 
             0 C

   clean up using the Formula to obtain 
             A 0
             0 C 
   where each of A and C is SL2; now find canonical
   generators for A and (1, 2); also (3, 4) for C */

MainTask := function (G, g, w)
   d := Degree (G);
   F := BaseRing (G);
   C := CentraliserOfInvolution (G, g, w);
   
   /* produce element h of form I J ; 0 I 
      where J is non-scalar */
   repeat 
      h, wh := PullbackInvolution (G, C, [1..2]);
      h := h^2; wh := wh^2;
      b := ExtractBlock (h,1,3,2,2);
      found := IsScalar (b) eq false and Rank (b) eq 2;
   until found;
   
   C2 := CentraliserOfInvolution (G, h, wh);

   T := sub < GL(d, F) | C, C2>;
   U := UserGenerators (C) cat UserGenerators (C2); 
   W := UserWords (C) cat UserWords (C2);
   _ := InitialiseGroup (T: generators := U, scalars:=false);
   T`UserWords := W;
   X, Y, Z, CB4 := FormulaABC (G, T, 2);

   AX := ExtractGroup (X, [1..2]);
   flag := RecognizeSL2 (AX, #BaseRing (AX): Verify := false);

   /* identify Chevalley basis for AX */
   a := GL(2, F) ! [0,1,1,0];
   a, wa := PullbackElement (G, X, AX, a);
   
   b1 := GL(2, F) ! [0,1,1,0];
   b1 := a; wb1 := wa;

   t := GL(2, F) ! [1,1,0,1];
   t, wt := PullbackElement (G, X, AX, t);

   delta := GL(2, F) ! [F.1,0,0,F.1^-1];
   delta, wdelta := PullbackElement (G, X, AX, delta);

   e1 := GL(2, F) ! [1,0, 1,1];
   e1, we1 := PullbackElement (G, X, AX, e1);

   AY := ExtractGroup (Y, [3..4]);
   flag := RecognizeSL2 (AY, #BaseRing (AY): Verify := false);

   a2 := GL(2, F) ! [0,1,1,0];
   a2, wa2 := PullbackElement (G, Y, AY, a2);

   e2 := GL(2, F) ! [1,1,0,1];
   e2, we2 := PullbackElement (G, Y, AY, e2);

   return [GL(d, F) | a, b1, t, delta], [wa, wb1, wt, wdelta],
          a2, wa2, [e1, e2], [we1, we2], CB4;
end function;

/* construct Chevalley basis for SL(4, q) */

SolveSL4 := function (G)

   d := Degree (G);
   assert d eq 4;

   _ := InitialiseGroup (G);

   inv, w := ConstructInvolution (G);
   assert Order (inv) eq 2;

   CB := InvolutionBaseChange (G, inv);
   G := ApplyCOB (G, CB);
   g := CB * inv * CB^-1;
   A, WA, b, wb, E, WE, cb := MainTask (G, g, w);

   g := &*E;
   wg := &*WE;

   assert g eq cb * G`SLPGroupHom(wg) * cb^-1;
   H := ApplyCOB (G, cb);
   glue, wglue := GlueSL4 (H, g, wg);

   A[2] := A[2] * glue * b;
   WA[2] := WA[2] * wglue * wb;

   return A, WA, cb * CB;
end function;
