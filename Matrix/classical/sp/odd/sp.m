StandardSpForm := function (n, q)
   assert IsEven (n);
   A := MatrixAlgebra (GF (q), 2);
   J := A![0,1,-1,0];
   m := n div 2;
   return DiagonalJoin ([J: i in [1..m]]);
end function;

StandardSp := function (n, q) 
   G := Sp (n, q);
   form := StandardSpForm (n, q);
   CB := TransformForm (form, "symplectic");
   return G^(CB^-1), form;
end function;

SpHalfChangeBasis := function (G, form, dim)
   F := BaseRing (G);
   q := #F;
   d := Degree (G);
   a := ExtractBlock (form, 1, 1, dim, dim);
   op := StandardSpForm (dim, q);
   x := TransformForm (a, "symplectic");
   y := TransformForm (op, "symplectic");
   a := x * y^-1;

   b := ExtractBlock (form, dim + 1, dim + 1, d - dim, d - dim);
   om := StandardSpForm (d - dim, q);
   x := TransformForm (b, "symplectic"); 
   y := TransformForm (om, "symplectic");
   b := x * y^-1;
   
   A := DiagonalJoin (a, b);
   
   return GL(d, F)!A;

end function;

/* additional element to generate all of Sp */

SpAdditionalElement := function (F)
   M := MatrixAlgebra (F, 4);
   I := Identity (M);

   I[2][3] := 1;
   I[4][1] := 1;

   I := GL (4, F)!I;
   return I;
end function;

/* canonical basis for Sp(d, q): if complete then add additional element */

SpChosenElements := function (G : Words := true)

   d := Degree (G);
   F := BaseRing (G); 

   w := PrimitiveElement (F);
   M := MatrixAlgebra (F, d);
   a := Identity (M);
   a[1][1] := 0;
   a[1][2] := 1;
   a[2][1] := -1;
   a[2][2] := 0;

   t := Identity (M);
   t[1][2] := 1;

   delta := Identity (M);
   delta[1][1] := w;
   delta[2][2] := w^-1;

   if d ge 4 then 
      p := Zero (M);
      p[1][3] := 1; p[2][4] := 1; p[3][1] := 1; p[4][2] := 1;
      for i in [5..d] do p[i][i] := 1; end for;
   else
      p := Identity (M);
   end if;

   if d ge 4 then 
      b := Zero (M);
      n := d div 2;
      for i in [1..d - 3 by 2] do
         b[i][i + 2] := 1;
      end for; 
      b[d - 1][1] := 1;
      for i in [2..d - 2 by 2] do
         b[i][i + 2] := 1;
      end for; 
      b[d][2] := 1;
   else 
      b := Identity (M);
   end if;

   P := GL(d, F);
   a := P!a; b := P!b; p := P!p; t := P!t; delta := P!delta;
   if d gt 4 then 
      v := P!(DiagonalJoin (Identity (MatrixAlgebra (F, d - 4)),
                            SpAdditionalElement (F)));
   elif d eq 4 then 
      v := SpAdditionalElement (F);
   else
      v := Identity (P);
   end if;

   if Degree (G) gt 2 then
      _, cb := ConjugateToStandardCopy (G, "symplectic");
   else
      cb := Identity (G);
   end if;

   if Words then 
      G`CentraliserTrees := [];
      T := CompositionTree (G: KernelRank := 10, KnownLeaf := true);
      flag, wa := SolveWord (T, T[1], a^(cb^-1)); 
      if not flag then G:Magma; error "Problem in SpChosenElements"; end if;
      flag, wb := SolveWord (T, T[1], b^(cb^-1)); 
      if not flag then G:Magma; error "Problem in SpChosenElements"; end if;
      flag, wp := SolveWord (T, T[1], p^(cb^-1)); 
      if not flag then G:Magma; error "Problem in SpChosenElements"; end if;
      flag, wt := SolveWord (T, T[1], t^(cb^-1)); 
      if not flag then G:Magma; error "Problem in SpChosenElements"; end if;
      flag, wdelta := SolveWord (T, T[1], delta^(cb^-1)); 
      if not flag then G:Magma; error "Problem in SpChosenElements"; end if;
      flag, wv := SolveWord (T, T[1], v^(cb^-1)); 
      if not flag then G:Magma; error "Problem in SpChosenElements"; end if;
      return [a, b, t, delta, p], [wa, wb, wt, wdelta, wp], (cb^-1);
   else 
      return [a, b, t, delta, p, v], (cb^-1), _;
   end if;
end function;

/* G group with basis which exhibits split as f, d - f;
   G1 is Sp(f) as f x f matrices;
   E1, W1 are elements, words for Sp(f);
   E1[2] = (1,3,5,...,f - 1) (2,4,6,...,f);
   similarly G2, E2, W2 describe Sp(d - f);
   if FinalCall is true, then this is the final glue 
   and we must obtain additional element to
   generate all of Sp */
   
SpGlue := function (G, G1, E1, W1, G2, E2, W2: FinalCall := false)

t3 := Cputime ();
   d := Degree (G);
   F := BaseRing (G); 
   q := #F;
   
   a := E1[1]; b1 := E1[2]; t := E1[3]; 
   wb1 := W1[2];
   
   /* top piece */
   f := Degree (G1);

   /* construct u = Diagonal ([1, 1, ..., -1, -1]) */
   o := q - 1;
   // delta := E1[4]; u := delta^(o div 2); u :=   u^( b1^((f - 2) div 2));
   wdelta := W1[4]; wu := wdelta^(o div 2); wu := wu^(wb1^((f - 2) div 2));

   /* construct v = Diagonal ([-1,-1, ..., 1, 1]) */

   // E2[2] = (f + 1,f + 3,5,...,d - 1) (f + 2,f + 4,...,f + d)
   b2 := E2[2]; wb2 := W2[2];
   // delta := E2[4]; v := delta^(o div 2); 
   wdelta := W2[4]; wv := wdelta^(o div 2); 

   /* w is word for 
      uv = Diagonal ([ 1, 1, ..., -1, -1, -1,-1, 1, 1, ..., 1])
      where -1s are in position f - 1, ..,f + 2 */
   w := wu * wv;

   vprint User5: "Time to construct w = u v ", Cputime (t3);

   /* set up matrix I for uv */
   M := MatrixAlgebra (F, d);
   I := Identity (M);
   for i in [f - 1..f + 2] do I[i][i] := -1; end for;
   I := GL(d, F) ! I;
 
   H := G;
t3 := Cputime ();

   /* construct centraliser Sp(4) x Sp(d - 4) in G of I */
   C := SecondSpecialCentraliser (G, I, w, {f - 1, f, f + 1, f + 2}: 
                                  IsCorrectType:= MyIsSymplecticGroup);
   vprint User5: "Time to construct Sp4 as centraliser is  ", Cputime (t3);
t3 := Cputime ();

   /* construct C = Sp(4) acting on {f - 1, f, f + 1, f + 2} */
   C := GoodCentraliser (G, C, 4, {1..f - 2} join {f + 3..d}:
                         IsCorrectType := MyIsSymplecticGroup);
   vprint User5: "Time to get Sp4 action on factor is  ", Cputime (t3);

   /* modify C to include u as generator */
   MA := MatrixAlgebra (F, d);
   u := Identity (MA);
   for i in [f-1..f] do u[i][i] := -1; end for;
   C := RedefineGroup (G, C, u, wu);

   /* set up Y = Sp(4) */
   Y := ExtractFactor (C, [f - 1..f + 2]);
   _ := InitialiseGroup (Y: generators := Y`UserGenerators, scalars:=false);

   q := #F;

   if (not FinalCall) and (q ne 3) then
      vprint User5: "We are in SL2 call";

      /* construct projective centraliser of Diagonal ([-1, -1, 1, 1])
         in Sp4; this is SL2 wr C2 */
    t3 := Cputime ();
      n := #Y`UserGenerators;
      m := Ngens (Y); 
      Cu := ThirdCentraliser (Y, Y.m, Y`SLPGroup.n: type := "symplectic",
                              IsCorrectType := MyIsSymplecticGroup);
      vprint User5: "time to get SL2 wr C2 centraliser is ", Cputime (t3);

   t3 := Cputime ();

      /* find SL2 x SL2 and wreathing element x in 
         SL2 wr C2 and its word wx */
      
      MyConstructSL2xSL2 := function (G)
         U := G`UserGenerators;
         for i in [1..#U] do
            if InBaseGroup (U[i]) eq false then
               x := U[i]; wx := G`UserWords[i];
             end if;
         end for;
         D := MyDerivedSubgroupWithWords (G);
         return D, x, wx;
      end function;

      /* wx is in Y`SLPGroup */
      L, x, wx := MyConstructSL2xSL2 (Cu);

      /* set up action of SL2 on each factor */
      sl2A := GoodCentraliser (Cu, L, 2, {3, 4}:
                               IsCorrectType := MyIsSymplecticGroup);
      A := ExtractFactor (sl2A, [1, 2]);
      sl2B := GoodCentraliser (Cu, L, 2, {1, 2}:
                               IsCorrectType := MyIsSymplecticGroup);
      B := ExtractFactor (sl2B, [3, 4]);

      /* multiply glue element by wreathing element 
         of SL wr C2 to obtain element of SL2 x SL2 */
      g := GlueElement (F);
      gx := g * x;
      assert InBaseGroup (gx);

      a := ExtractAction (gx, [1, 2]);
      b := ExtractAction (gx, [3, 4]);
      assert Determinant (a) eq 1 and Determinant (b) eq 1;
   
      flag := RecognizeSL2 (A, #BaseRing (A): Verify := false);
      flag, wa := MySL2ElementToWord (A, a);
      flag := RecognizeSL2 (B, #BaseRing (B): Verify := false);
      flag, wb := MySL2ElementToWord (B, b);

      vprint User5: "Time to get down to SL2 is ", Cputime (t3);

      /* trace words for glue element back to G */

      /* A -> sl2A */
      wa := ImagesOfWords (A, sl2A, [wa]);
      wa := wa[1];
 
      /* B -> sl2B */
      wb := ImagesOfWords (B, sl2B, [wb]);
      wb := wb[1];

      /* sl2* -> Cu */
      T := Cu`SLPGroup;
      gamma := hom < sl2A`SLPGroup -> T | sl2A`UserWords>;
      wa := gamma (wa);

      T := Cu`SLPGroup;
      gamma := hom < sl2B`SLPGroup -> T | sl2B`UserWords>;
      wb := gamma (wb);

      /* identify glue element in SL2 wr C2 */
      wg := wa * wb; 

      /* SL2 wr C2 to Sp4 */
      T := Y`SLPGroup;
      gamma := hom < Cu`SLPGroup -> T | Cu`UserWords>;
      wg := gamma (wg);
      wg := wg * wx^-1;
   else 
      t3 := Cputime ();
      vprint User5: "Composition Tree call for degree", Degree (Y);
      T := CompositionTree (Y: KernelRank := 10, KnownLeaf := true);
      g := GlueElement (F);
      flag, wg := SolveWord (T, T[1], g);

      add := SpAdditionalElement (F);
      flag, wadd := SolveWord (T, T[1], add);

      /* SL4 to C */
      wadd := ImagesOfWords (Y, C, [wadd]);
      wadd := wadd[1];

      /* C to G */
      T := G`SLPGroup;
      gamma := hom <C`SLPGroup -> T | C`UserWords cat [wu]>;
      wadd := gamma (wadd);
      Add := Identity (MA);
      InsertBlock (~Add, add, f - 1, f - 1);
      vprint User5: "Total Time in Composition Tree is ", Cputime (t3);
   end if; 

   /* Sp4 to C */
   wg := ImagesOfWords (Y, C, [wg]);
   wg := wg[1];

   /* C to G */
   T := G`SLPGroup;
   gamma := hom < C`SLPGroup -> T | C`UserWords cat [wu]>;
   wg := gamma (wg);

   /* set up basis elements and words for G */
   basis := SpChosenElements (G: Words := false);

   A := basis[1];
   wa := W1[1]; 

   B1 := Identity (M);
   b1 := E1[2]; 
   MB := MatrixAlgebra (F, Nrows (b1));
   InsertBlock (~B1, MB!b1, 1, 1);
   B1 := GL(d, F)!B1; 
   wb1 := W1[2]; 

   Bg := Zero (M);
   Bg[f-1][f + 1] := 1; 
   Bg[f][f + 2] := 1;
   Bg[f + 1][f - 1] := 1;
   Bg[f + 2][f] := 1;
   for i in [1..f - 2] cat [f + 3..d] do Bg[i][i] := 1; end for;
   Bg := GL(d, F)!Bg; 
    
   b2 := E2[2]; 
   B2 := Identity (M);
   MB := MatrixAlgebra (F, Nrows (b2));
   InsertBlock (~B2, MB!b2, f + 1, f + 1);
   B2 := GL(d, F)!B2; 
   wb2 := W2[2];

   /* produce (1,3,...,d - 1)(2,4,...,d) */
   B := B2 * Bg * B1;
   wb := wb2 * wg * wb1; 
   B := GL(d, F)!B; 

   T := basis[3];
   wt := W1[3]; 

   D := basis[4];
   wdelta := W1[4];

   if d gt 4 then 
      P := basis[5];
      wp := W1[5]; 
   else
      P := B;
      wp := wb;
   end if;

   gl := GL(d, F);
   E := [gl!A, gl!B, gl!T, gl!D, gl!P];
   W := [wa, wb, wt, wdelta, wp];

   /* additional element to generate symplectic group */
   if FinalCall then Append (~E, basis[6]); 
      o := (d - f - 2) div 2; wadd := wadd^(wb^o);
      Append (~W, wadd); 
   end if;

   vprint User5: "Time to get n-cycle and construct words is  ", Cputime (t3);
   return E, W;

end function;

/* recognize Sp in its natural representation */

SpProcess := function (G, InputDimension: Scalars := false, Special := false)

   _ := InitialiseGroup (G: scalars := Scalars, generators := UserGenerators (G));
   d := Degree (G);
   F := BaseRing (G);

   if (Degree (G) eq 2) then 
      // "Call CompositionTree for degree ", d;
      X, Y, CB := SpChosenElements (G);
      return X, Y, CB;
   end if;

   /* if special, then split space of degree d = 4k + r as 4k and r */
   if Special then 
      r := d mod 4;
      if r eq 0 then 
         Range := [Degree (G) div 2]; 
         g, w, H, b, CB, dim := SpecialSplitSpace (G:
                                  IsCorrectType:= MyIsSymplecticGroup);
      else 
         Range := [Degree (G) - r]; 
         g, w, H, b, CB, dim := SplitSpace (G: Range := Range);
      end if;
   else 
      Range := [Degree(G) div 3..2 * Degree(G) div 3];
      if Degree (G) eq 4 then Range := [2]; end if;
      g, w, H, b, CB, dim := SplitSpace (G: Range := Range);
   end if;

   flag, form := SymplecticForm (G);
   form := CB * form * Transpose (CB);
   cb := SpHalfChangeBasis (G, form, dim);
   cb := cb^-1;
   H := H^(cb^-1);

   H`SLPGroup := G`SLPGroup;
   H`UserGenerators := [cb * CB * x * CB^-1 * cb^-1: x in UserGenerators (G)];
   H`SLPGroupHom := MyHom (H, H`SLPGroup, UserGenerators (H));

t1 := Cputime ();
    C := SpecialCentraliser (H, b, w, dim:
                             IsCorrectType:= MyIsSymplecticGroup);
t1 := Cputime ();
   C1 := GoodCentraliser (G, C, dim, {dim + 1..d}:
                          IsCorrectType := MyIsSymplecticGroup);
   C2 := GoodCentraliser (G, C, d - dim, {1..dim}:
                          IsCorrectType := MyIsSymplecticGroup);

   G1 := ExtractFactor (C1, {1..dim});
   G2 := ExtractFactor (C2, {dim + 1..d});

   E1, W1, CB1 := $$ (G1, InputDimension: Special := Special);
   // if Degree (G1) gt 2 then assert Verify (G1, E1, W1, CB1); end if;

   /* pull back words to G */
   W1 := [FactorToParent (G, C1, W1[i]): i in [1..#W1]];
   
   /* if special we can conjugate solution for G1 under element 
      of projective centraliser to obtain solution for G2 */

   if Special and (Degree (G) mod 4 eq 0) then 
      // "Search for projective generator";
      theta, wtheta := ProjectiveGenerator (G, g, w);
      theta := cb * CB * theta * CB^-1 * cb^-1;
      /* now conjugate */
      W2 := [w^wtheta: w in W1]; 
      E2 := E1;
      LCB1 := CombineMatrices (CB1, CB1^0);
      B2 := [LCB1[i] : i in [1..dim]] cat [LCB1[i] * theta : i in [1..dim]];
      LCB2 := GL(d, F) ! &cat [Eltseq (b2): b2 in B2];
      CB2 := ExtractBlock (LCB2, dim + 1, dim + 1, dim, dim);
   else 
      // "call 2";
      E2, W2, CB2 := $$ (G2, InputDimension: Special := Special);
      // if Degree (G2) gt 2 then assert Verify (G2, E2, W2, CB2); end if;
      W2 := [FactorToParent (G, C2, W2[i]): i in [1..#W2]];
   end if;

   Total := CombineMatrices (CB1, CB2);
   H := ApplyCOB (G, Total * cb * CB);

t1 := Cputime ();
   // "call Glue", Degree (G1), Degree (G2);
   X, Y := SpGlue (H, G1, E1, W1, G2, E2, W2: 
                   FinalCall := Degree (H) eq InputDimension);
   // assert Verify (G,X,Y,Total * CB);

"time to glue is ", Cputime (t1);
   return X, Y, Total * cb * CB;
end function;

/* construct Steinberg generators of G */

SolveSp := function (G: Special := true)
   d := Degree (G);
   E, W, CB := SpProcess (G, d: Scalars := true, Special := Special);
   return E, W, CB;
end function;
