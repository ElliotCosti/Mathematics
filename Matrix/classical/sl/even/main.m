/* permitted values for smaller SL (e, q) to construct as 
   subgroup of SL (d, q) */

SmallerRanks := function (d)
   if d eq 9 then return [4, 5]; 
   elif d eq 10 then return [4, 5]; 
   elif d eq 11 then return [4, 5];
   elif d eq 13 then return [4, 5, 8, 9];
   elif d eq 17 then return [8, 9, 12, 13];
   else 
      return [x : x in [5 * d div 9 .. 7 * d div 9] | x mod 4 in {0, 1}];
   end if;
end function;

/* Steinberg basis for SL(d, q) */

ChosenElements := function (G : Words := true)
   d := Degree (G);
   F := BaseRing (G); 

   w := PrimitiveElement (F);
   M := MatrixAlgebra (F, d);
   a := Identity (M);
   a[1][1] := 0;
   a[1][2] := 1;
   a[2][1] := -1;
   a[2][2] := 0;

   b := Zero (M);
   for i in [2..d] do
      b[i][i - 1] := -1;
   end for;
   b[1][d] := 1;
 
   t := Identity (M);
   t[1][2] := 1;

   delta := Identity (M);
   delta[1][1] := w;
   delta[2][2] := w^-1;

   P := GL(d, F);
   a := P!a; b := P!b; t := P!t; delta := P!delta;

   if Words then 
      G`CentraliserTrees := [];
      T := CompositionTree (G: KernelRank := 10, KnownLeaf := true);
      repeat flag, wa := SolveWord (T, T[1], a); until flag;
      repeat flag, wb := SolveWord (T, T[1], b); until flag;
      repeat flag, wt := SolveWord (T, T[1], t); until flag;
      repeat flag, wdelta := SolveWord (T, T[1], delta); until flag;
      return [a, b, t, delta], [wa, wb, wt, wdelta];
   else 
      return [a, b, t, delta];
   end if;
 
end function;

SpinElement := function (G, A, y, w, m)
   d := Degree (A);
                                                                                
   /* construct element of corank m */
   while Corank (y) lt m do
      a, wa := RandomWord (A);
      wa := PullbackWord (G, A, wa);
      b, wb := RandomWord (A);
      wb := PullbackWord (G, A, wb);
      flag, y, w := Variations (y^a, w^wa, y^b, w^wb, 2: Equality := false);
      "Corank is now ", Corank (y);
   end while;
                                                                                
   return y, w;
end function;

/* given an involution of corank m, construct using the Formula
   SL (m, q), SL(d - 2m, q), SL(m, q) */

ThreeSLs := function (G, g, w, m)
   d := Degree (G);
   F := BaseRing (G);
   C := CentraliserOfInvolution (G, g, w);

   /* centraliser is A * *; 0 B *; 0 0 A;
      apply formula to construct A and B as SLs */
   h, wh, COB := FormulaElement (G, C, m);

   A, B := FormulaAB (G, C, m, h, wh, COB);

   /* produce involution h of form I 0 J ; 0 I 0; 0 0 I  where 
      J is of rank m and is independent from same block in g */
   s := ExtractBlock (g, 1, d - m + 1, m, m);
   repeat 
      h, wh := PullbackInvolution (G, A, [1..m] : 
               SmallerCorank := true, Small := false);
      h := h^2; wh := wh^2;
      if Corank (h) gt 0 then 
         h, wh := SpinElement (G, A, h, wh, m);
      end if;
      r := ExtractBlock (h, 1, d - m + 1, m, m);
   until Corank (h) eq m and IsScalar (r * s^-1) eq false;
   
   assert Corank (h) eq m;

   /* now compute its centraliser of form A * * ; 0 B * ; 0 0 A' */
   C2 := CentraliserOfInvolution (G, h, wh);
   h2, wh2, COB2 := FormulaElement (G, C2, m);
//   assert h2 eq COB2 * C2`SLPGroupHom (wh2) * COB2^-1;

//   wh2 := PullbackWord (G, C2, wh2);
//   assert h2 eq COB2 * G`SLPGroupHom (wh2) * COB2^-1;
//   A2, B2 := FormulaAB (G, C2, m, h2, wh2, COB2);

   T := sub < GL(d, F) | C, C2>;
   U := UserGenerators (C) cat UserGenerators (C2); 
   W := UserWords (C) cat UserWords (C2);

   _ := InitialiseGroup (T: generators := U, scalars:=false);
   T`UserWords := W;
   "Apply Formula ABC in ThreeSLs to degree ", Degree (T);
   X, Y, Z, CB4 := FormulaABC (G, T, m);
   return X, Y, Z, CB4;
end function;

/* produce matrix of rank d containing diagonal blocks X, Y, Z */

CombineMatrices := function (G, X, Y, Z)
   d := Degree (G);
   F := BaseRing (G);
   M := MatrixAlgebra (F, d);
   CB := Identity (M);
   InsertBlock (~CB, X, 1, 1);
   InsertBlock (~CB, Y, Nrows (X) + 1, Nrows (X) + 1);
   InsertBlock (~CB, Z, Nrows (X) + Nrows (Y) + 1, Nrows (X) + Nrows (Y) + 1);
   return GL(d, F) ! CB;
end function;

/* given H = SL(rank, q) <= G = SL(d, q), construct involution of corank 
   m = rank div 2 and return SL(m), SL(d - 2m), SL(m) as subgroups of G */

SplitUpSL := function (G, H, rank, CB)
   m := rank div 2;
   d := Degree (G);
   F := BaseRing (G);
   inv, w := PullbackInvolution (G, H, [1..rank]: Evaluation := false);
   g := CB^-1 * inv * CB; 
   assert Corank (inv) eq m;

   CBI := InvolutionBaseChange (G, g);
   g := GL(d, F) ! (CBI * g * CBI^-1);
   G := ApplyCOB (G, CBI);
   X, Y, Z, CB1 := ThreeSLs (G, g, w, m);
   return X, Y, Z, CB1 * CBI;

end function;

/* I involution, fp is fixed point free element;
   its centraliser is A  *  *    where A is SL2, B is SL(d - 2);
                      0  B  * 
                      0  0  A 
   
   clean up to construct A 0 *   where A is SL2   
                         0 I 0 
                         0 0 A                     
*/     

GetSL2 := function (H, I, wI, CBI, fp, wfp: SpecialGlue := false)
   d := Degree (H);
   F := BaseRing (H);
   H := ApplyCOB (H, CBI);
   h := GL(d, F) ! (CBI * I * CBI^-1);
   C := CentraliserOfInvolution (H, h, wI);

   if SpecialGlue then 
      /* must use linear algebra to clean up centraliser since we could
         not construct fpf element, dimension of one piece is 3 */
      gensC, W := GeneralLinearProblem (H, C, 2);
   else 
      /* use the formula to clean up centraliser */
      FP := CBI * fp * CBI^-1;
      CC := KillFactor (H, C, [[1,2], [d - 1, d]], [[3..d - 2]]:Words:=true);
      U := UserGenerators (CC);
      gensC := [Formula (FP, U[i]): i in [1..#U]];
      W := CC`UserWords;
      W := [FormulaWord (wfp, W[i], Order (fp)): i in [1..#W]];
   end if;

   // "gensC is ", gensC;
   D := sub <GL (d, F) | gensC>;
   _ := InitialiseGroup (D : generators := gensC, scalars := false);

   E := ExtractGroup (D, [1, 2, d - 1, d]);
   E`UserWords := W;
   return E, CBI;
end function;

/* I is involution, word wI; fp, wpf fixed point free element;
   extract action of I on 4 rows determined by index,
   this action is   0 1 0 0  perform base change to obtain 1 0 1 0
                    1 1 0 0                                0 1 0 1
                    0 0 1 1                                0 0 1 0 
                    0 0 0 1                                0 0 0 1

   construct centraliser of I to give  A  *  
                                       0  A
    where A is SL2 blocks;
    now find another involution of corank 2 and compute its
    centraliser  A' *   
                 0  B' 
    The group generated by these two is A  *  
                                        0  B  
    for arbitrary SL2 blocks A, B and contains glue 
                      0  1  0  0
                      1  0  0  0
                      0  0  1  0
                      0  0  0  1   
*/
         
Glue := function (G, TotalCB, H, I, wI, fp, wfp, index: SpecialGlue := false)

   "first call to GetSL2";
   CBI := InvolutionBaseChange (H, I);

   time E := GetSL2 (H, I, wI, CBI, fp, wfp: SpecialGlue := SpecialGlue);

   t := Cputime ();
   i := ExtractAction (I, [index - 1, index, index + 1, index + 2]);
   repeat 
      I2, wI2 := PullbackInvolution (G, E, [1,2] : ParentWord := true);
      I2 := I2^2; wI2 := wI2^2;
   until Corank (I2) eq 2; 
   "Time to obtain and evaluate second involution in Glue is ", Cputime (t);

   block := ExtractBlock (I2, 1, 3, 2, 2);
   d := Degree (H);
   F := BaseRing (H);
   MA := MatrixAlgebra (F, d);
   I2 := Identity (MA);
   InsertBlock (~I2, block, 1, d - 1);
   I2 := GL(d, F) ! (CBI^-1 * I2 * CBI);
//   assert TotalCB * G`SLPGroupHom (wI2) * TotalCB^-1  eq I2;

   "second call to GetSL2";
   time E2 := GetSL2 (H, I2, wI2, CBI, fp, wfp: SpecialGlue := SpecialGlue);
   
   F := BaseRing (G);

   T := sub < GL(4, F) | E, E2>;
   U := UserGenerators (E) cat UserGenerators (E2);
   W := UserWords (E) cat UserWords (E2);
   _ := InitialiseGroup (T: generators := U, scalars:=false);
   T`UserWords := W;

   glue, wglue := LinearProblem (G, T);
   return glue, wglue;
end function;

OrganiseGlue := function (G, TotalCB, m, index, option, 
                SX, X, A, WA, SZ, Z, B, WB, SY, Y, C, WC)

   /* construct involution to obtain SL4 and glue */
   g1 := (A[1]^A[3])^(A[2]^2);
   wg1 := (WA[1]^WA[3])^(WA[2]^2);
   wg1 := ImagesOfWords(X, SX, [wg1])[1];
   wg1 := PullbackWord (G, SX, wg1);

   g2 := B[3];
   wg2 := WB[3];
   wg2 := ImagesOfWords(Z, SZ, [wg2])[1];
   wg2 := PullbackWord (G, SZ, wg2);

   d := Degree (G);
   F := BaseRing (G);
   MA := MatrixAlgebra (F, d);
   I := Id (MA);
   InsertBlock (~I, g1, index - Nrows (g1) + 1, index - Nrows (g1) + 1);
   InsertBlock (~I, g2, index + 1, index + 1);
   wI := wg1 * wg2; 
   // assert I eq TotalCB * G`SLPGroupHom (wI) * TotalCB^-1;

   /* if possible construct fixed point free elements */
   if Degree (Z) ne 3 and Degree (Y) ne 3 and Degree (X) ne 3 then 
      fpa, wfpa := ProduceFPF (G, SX, X, A, WA, Degree (X), 1);
      fpb, wfpb := ProduceFPF (G, SZ, Z, B, WB, Degree (Z), 2);
      fpc, wfpc := ProduceFPF (G, SY, Y, C, WC, Degree (Y) + 2, 1: 
                               cycle := [* C[2], WC[2]*]);

      wfp := wfpa * wfpb * wfpc;
      if option eq 1 then 
         fp := CombineMatrices (G, fpa, fpb, fpc);
      else 
         fp := CombineMatrices (G, fpc, fpa, fpb);
      end if;
      SpecialGlue := false;
   else 
      SpecialGlue := true;
      fp := false; wfp := false;
   end if;
   // assert fp eq TotalCB * G`SLPGroupHom (wfp) * TotalCB^-1;

   H := ApplyCOB (G, TotalCB);

   /* find glue element */
t := Cputime ();
   glue, wglue := Glue (G, TotalCB, H, I, wI, fp, wfp, index: 
                        SpecialGlue := SpecialGlue);
"time in Glue procedure", Cputime (t);

   return glue, wglue;

end function;

/* base cases for recursion */

SolveSmaller := function (X)
   if Degree (X) in [2, 3] then
      A, WA := ChosenElements (X);
      CA := Identity (X);
   elif Degree (X) eq 4 then 
      A, WA, CA := SolveSL4 (X);
   elif Degree (X) eq 5 then 
      A, WA, CA := SolveSL5 (X);
   else 
      error "Function called for wrong dimension";
   end if;
   return A, WA, CA;
end function;

/* verify that numerical conditions are correct for split */

CheckSplit := function (d, rank, SX, SY, SZ)

   S := Sections (SX);
   degs := [Degree (s): s in S];
   m := Maximum (degs);
   if IsEven (d) then assert IsEven (m); end if;
   S := Sections (SY);
   degs := [Degree (s): s in S];
   n := Maximum (degs);
   if m eq 1 or m ne n then error "failure to split correctly"; end if;
   if m ne rank div 2 then "m is only ", m; assert m eq rank div 2; end if;
   S := Sections (SZ);
   degs := [Degree (s): s in S];
   r := Maximum (degs);
   if r ne d - 2 * m then error "failure to split correctly"; end if;
   return true, m;
end function;

EvenMain := function (G: Scalars := false)

    _ := InitialiseGroup (G: scalars := Scalars, generators := UserGenerators (G));

   d := Degree (G);
   "Input has degree ", d;
   if d le 5 then return SolveSmaller (G); end if;

   ranks := SmallerRanks (d);
   t := Cputime ();
   H, rank, SmallerCOB := ConstructSmallerSL (G, ranks);
   "time to construct smaller SL of rank ", rank, " is ", Cputime (t);

   "now construct 3 SLs";
   t := Cputime ();
   SX, SY, SZ, COB := SplitUpSL (G, H, rank, SmallerCOB);
   "Time to construct 3 SLs is ", Cputime (t);

//   COB := COB * SmallerCOB;

//   m := rank div 2;

   flag, m := CheckSplit (d, rank, SX, SY, SZ);

   X := ExtractGroup (SX, [1..m]);
   t := Cputime ();
   "Solve first SL of rank ", m;
   A, WA, CA := $$ (X: Scalars := false);
//   A, WA, CA := Main (X: Scalars := false);
   "time to solve first SL of rank ",  m, " is ", Cputime (t);

   "Solve second SL of rank ", d - 2 * m;
   t := Cputime ();
   Z := ExtractGroup (SZ, [m + 1 .. d - m]);
   B, WB, CB := $$ (Z: Scalars := false);
//   B, WB, CB := Main (Z: Scalars := false);
   "time to solve second SL of rank ", d - 2 * m, " is ", Cputime (t);

   "Solve third SL of rank ",  m;
   t := Cputime ();
   Y := ExtractGroup (SY, [d - m + 1 .. d]);
   time C, WC, CC := $$ (Y: Scalars := false);
//   C, WC, CC := Main (Y: Scalars := false);
   "time to solve third SL of rank ", m, " is ", Cputime (t);

   total := CombineMatrices (G, CA, CB, CC);
   TotalCB := total * COB;

   "Solve for first glue element";
   t := Cputime ();
   option := 1;
   glue, wglue := OrganiseGlue (G, TotalCB, m, m, option,
                SX, X, A, WA, SZ, Z, B, WB, SY, Y, C, WC);
   "time to find first glue element is ", Cputime (t);
   
   "Solve for second glue element";
   t := Cputime ();
   option := 2; index := d - m;
   glue2, wglue2 := OrganiseGlue (G, TotalCB, m, index, option,
                       SZ, Z, B, WB, SY, Y, C, WC, SX, X, A, WA );
   "time to find second glue element is ", Cputime (t);

   PullbackBasisElement := function (G, SX, X, A, WA, index) 
      a := A[index];
      wa := WA[index];
      wa := ImagesOfWords(X, SX, [wa])[1];
      wa := PullbackWord (G, SX, wa);
      return a, wa;
   end function;

   "Set up Steinberg basis";
   N := [];
   for i in [1,3,4] do 
      a, N[i] := PullbackBasisElement (G, SX, X, A, WA, i);
   end for;

   xcycle, wxcycle := PullbackBasisElement (G, SX, X, A, WA, 2);
   zcycle, wzcycle := PullbackBasisElement (G, SZ, Z, B, WB, 2);
   ycycle, wycycle := PullbackBasisElement (G, SY, Y, C, WC, 2);
//   g := xcycle * glue * zcycle * glue2 * ycycle;
   wg := wxcycle * wglue * wzcycle * wglue2 * wycycle;

   N[2] := wg;

   Chosen := ChosenElements (G:Words := false);
   return Chosen, N, TotalCB; 
end function;

SolveEvenSL := function (G)
   F := BaseRing (G);
   if IsOdd (#F) then error "Even characteristic only"; end if;
   if #F eq 2 then error "Use for field size at least 4"; end if; 
   return EvenMain (G: Scalars := true);
end function;
