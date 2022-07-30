/* G group with basis which exhibits split as f, d - f;
   G1 is SO+(f) as f x f matrices;
   E1, W1 are elements, words for SO+(f);
   similarly G2, E2, W2 describe SO+(d - f); */
   
SOPlusSpecialGlue := function (G, G1, E1, W1, G2, E2, W2)

   d := Degree (G);
   F := BaseRing (G); 
   q := #F;
   
   /* top piece */
   f := Degree (G1);

   /* construct word for 
      Diagonal ([ 1, 1, ..., -1, -1, -1,-1, 1, 1, ..., 1])
      where -1s are in position f - 1, ..,f + 2 */

   w := W2[#W2];
   pow := (f - 2) div 2;
   w := w^(W1[#W1 - 1]^pow);

   /* set up matrix I for w */
   M := MatrixAlgebra (F, d);
   I := Identity (M);
   for i in [f - 1..f + 2] do I[i][i] := -1; end for;
   I := GL(d, F) ! I;
 
   /* construct centraliser SO+(4) x SO+(d - 4) in G of I */
   found := true;
   trial := 5;
   repeat 
      trial -:= 1;
      C4 := SOCentraliser (G, I, w, {f - 1, f, f + 1, f + 2});

      /* construct C = SO+(4) acting on {f - 1, f, f + 1, f + 2} */
      C := SOGoodCentraliser (G, C4, 4, {1..f - 2} join {f + 3..d});
      if d eq 8 and C cmpeq false then 
         found := false;
      end if;
   until found or trial eq 0;

   if trial eq 0 and Type (C) eq BoolElt then 
      C4: Magma; error "Failed to construct SO+4 as subgroup"; 
   end if;

   /* set up Y = SO+(4) */
   Y := ExtractFactor (C, [f - 1..f + 2]);
   _ := InitialiseGroup (Y: generators := Y`UserGenerators, scalars:=false);

   t3 := Cputime ();
   vprint User5: "Composition Tree call for degree", Degree (Y);
   T := CompositionTree (Y: KernelRank := 10);
   g := SOPlusGlueElement (F);
   flag, wg := SolveWord (T, T[1], g);

   /* C to G */
   T := G`SLPGroup;
   gamma := hom <C`SLPGroup -> T | C`UserWords cat [w]>;
   vprint User5: "Total time in Composition Tree is ", Cputime (t3);

   /* SO+4 to C */
   wg := ImagesOfWords (Y, C, [wg]);
   wg := wg[1];

   /* C to G */
   T := G`SLPGroup;
   gamma := hom < C`SLPGroup -> T | C`UserWords cat [w]>;
   wg := gamma (wg);

   /* set up basis elements and words for G */
   E := PlusChosenElements (G: Words := false);

   word := (W2[8] * wg * W1[8]);

   W := [W1[i] : i in [1..7]] cat [word];

   return E, W;

end function;

/* recognize SO+(d, q) where q = 3 mod 4 in its natural representation */

SOPlusSpecialProcess := function (G : Limit := 100, Special := false, 
                                      SpecialGroup := true)

   _ := InitialiseGroup (G);

   d := Degree (G);
   F := BaseRing (G);

   if (Degree (G) le 4) then 
      vprint User5: "Call CompositionTree for degree ", d;
      X, Y, CB := PlusChosenElements (G: SpecialGroup := SpecialGroup);
      return X, Y, CB;
   end if;

   /* if special, then split space of degree d = 4k + r as 4k and r */
   if Special then 
      r := d mod 4;
      if r eq 0 then 
         Range := [Degree (G) div 2]; 
         g, w, H, b, CB, dim := SOSpecialSplitSpace (G);
      else 
         Range := [Degree (G) - r]; 
         g, w, H, b, CB, dim := SOSplitSpace (G: Range := Range);
      end if;
   else 
      Range := [Degree(G) div 3..2 * Degree(G) div 3];
      if Degree (G) eq 4 then Range := [2]; end if;
      g, w, H, b, CB, dim := SOSplitSpace (G: Range := Range);
   end if;

   vprint User5: "Now sort out new form";
   flag, form := OrthogonalForm (G);
   form := CB * form * Transpose (CB);
   cb := SOFormBaseChange (G, form, dim: type := "orthogonalplus");

   cb := cb^-1;
   H := H^(cb^-1);

   H`SLPGroup := G`SLPGroup;
   H`UserGenerators := [cb * CB * x * CB^-1 * cb^-1: x in UserGenerators (G)];
   H`SLPGroupHom := MyHom (H, H`SLPGroup, UserGenerators (H));

   found := true; trial := 5; MinGens := 2; offset := 6;
   repeat 
      vprint User5: "Trial in SOSpecialProcess is ",  trial;
      trial -:= 1;
      if d eq 8 and dim eq 4 then MinGens +:= offset; end if;
      C := SOCentraliser (H, b, w, [1..dim]: MinGens := MinGens, 
                  Partial := true, SpecialGroup := SpecialGroup);

      C1 := SOGoodCentraliser (G, C, dim, {dim + 1..d});
      if (d eq 6) or (d eq 8 and dim eq 4) then
         found := not (C1 cmpeq false);
      elif C1 cmpeq BoolElt then
         C:Magma; error "Failed to construct subgroup";  
      end if;
      if found then 
         C2 := SOGoodCentraliser (G, C, d - dim, {1..dim});
         if d eq 6 or (d eq 8 and dim eq 4) then
            found := not (C2 cmpeq false);
         elif C2 cmpeq BoolElt then
            C:Magma; error "Failed to construct subgroup";  
         end if;
      end if;
   until found or trial eq 0;
   if not found or trial eq 0 then 
      error "Failure to construct two factors"; 
   end if;

   G1 := ExtractFactor (C1, {1..dim});
   G2 := ExtractFactor (C2, {dim + 1..d});

   flag, form1 := SymmetricBilinearForm (G1);
   assert flag;

   flag, form2 := OrthogonalForm (G2);
   assert flag;

   nmr := 0;
   found := false;
   repeat
      x, w := RandomWord (C);
      nmr +:= 1;
      o := Order (x);
      if IsOdd (o div 2) then 
         x := x^(o div 2);
         b1 := ExtractBlock (x, 1, 1, dim, dim);
         b2 := ExtractBlock (x, dim+1, dim+1, d - dim, d - dim);
         B := [* b1, b2 *];
         f1 := SpinorNorm (GL(Nrows (B[1]), F)! B[1], form1);
         f2 := SpinorNorm (GL(Nrows (B[2]), F)! B[2], form2);
         found := f1 eq 1 and f2 eq 1 and Determinant (B[1]) eq 1
                  and Determinant (B[2]) eq 1;
      end if;
   until found or nmr gt 10 * Limit;
   if nmr gt 10 * Limit then
      C:Magma;
      error "Failed to find good element in SOSpecialProcess";
   end if;
   vprint User5: "Required ", nmr, "elements to find good one";

   w := w^(o div 2);
   w := FactorToParent (G, C, w);

   D1 := sub <GL(d, F) | C1, x>;
   D1`UserGenerators := C1`UserGenerators cat [x];
   D1`UserWords := C1`UserWords cat [w];
   D1`SLPGroup := SLPGroup (#D1`UserGenerators);
   D1`SLPGroupHom := MyHom (D1, D1`SLPGroup, UserGenerators (D1));
   C1 := D1;

   G1 := ExtractFactor (C1, {1..dim});

   vprint User5: "Call 1 SOPlusSpecial Dimension of G1 is ", Degree (G1);
   E1, W1, CB1 := SOPlusProcess (G1, d: Special := Special, 
                                        SpecialGroup := true);
   // assert Verify (G1, E1, W1, CB1); 

   /* pull back words to G */
   W1 := [FactorToParent (G, C1, W1[i]): i in [1..#W1]];

   rem := d - dim;
   h := H`SLPGroupHom (W1[#W1]);

   D2 := sub < GL(d, F) | C2, h>;
   D2`UserGenerators := C2`UserGenerators cat [h];
   D2`UserWords := C2`UserWords cat [W1[#W1]];
   D2`SLPGroup := SLPGroup (#D2`UserGenerators);
   D2`SLPGroupHom := MyHom (D2, D2`SLPGroup, UserGenerators (D2));
   C2 := D2;
   G2 := ExtractFactor (C2, {dim + 1..d});

   /* if special we can conjugate solution for G1 under element 
      of projective centraliser to obtain solution for G2 */

   if Special and (Degree (G) mod 4 eq 0) then 
      vprint User5: "Search for projective generator";
      theta, wtheta := ProjectiveGenerator (G, g, w);
      theta := cb * CB * theta * CB^-1 * cb^-1;
      // now conjugate 
      W2 := [w^wtheta: w in W1]; 
      E2 := E1;
      LCB1 := CombineMatrices (G, CB1, CB1^0);
      B2 := [LCB1[i] : i in [1..dim]] cat [LCB1[i] * theta : i in [1..dim]];
      LCB2 := GL(d, F) ! &cat [Eltseq (b2): b2 in B2];
      CB2 := ExtractBlock (LCB2, dim + 1, dim + 1, dim, dim);
   else 
      vprint User5: "Call 2 SOPlusSpecial Dimension of G2 is ", Degree (G2);
      E2, W2, CB2 := SOPlusProcess (G2, d: SpecialGroup := true, Special := Special);
      // assert Verify (G2, E2, W2, CB2); 
      W2 := [FactorToParent (G, C2, W2[i]): i in [1..#W2]];
   end if;

   Total := CombineMatrices (CB1, CB2);
   H := ApplyCOB (G, Total * cb * CB);

   // w := W2[#W2];

   t1 := Cputime ();
   vprint User5: "Call SpecialSOPlusGlue", Degree (G1), Degree (G2);
   X, Y := SOPlusSpecialGlue (H, G1, E1, W1, G2, E2, W2); 
   // assert Verify (G,X,Y,Total * cb * CB);

   vprint User5: "Time in SpecialSOPlusGlue is ", Cputime (t1);
   return X, Y, Total * cb * CB;
end function;
