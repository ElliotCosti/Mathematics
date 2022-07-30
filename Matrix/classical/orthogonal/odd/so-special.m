/* G group with basis which exhibits split as f, d - f;
   G1 is SO+(f) as f x f matrices;
   E1, W1 are elements, words for SO+(f);
   E1[2] = (1,3,5,...,f - 1) (2,4,6,...,f);
   similarly G2, E2, W2 describe SO+(d - f); */
   
SOSpecialGlue := function (G, G1, E1, W1, G2, E2, W2)

   d := Degree (G);
   F := BaseRing (G); 
   q := #F;
   
   /* top piece */
   f := Degree (G1);

   /* construct word for 
      Diagonal ([ 1, 1, ..., -1, -1, -1,-1, 1, 1, ..., 1])
      where -1s are in position f - 1, ..,f + 2 */

   w := W2[#W2]^W2[#W2 - 1];
   pow := (f - 2) div 2;
   w := w^(W1[#W1 - 1]^pow);

   /* set up matrix I for w */
   M := MatrixAlgebra (F, d);
   I := Identity (M);
   for i in [f - 1..f + 2] do I[i][i] := -1; end for;
   I := GL(d, F) ! I;

/* 
"NOW COMPUT ";
JJ := G`SLPGroupHom (w);
JJ;
assert I eq  JJ;
*/

   H := G;

   t3 := Cputime ();
   /* construct centraliser SO+(4) x SO+(d - 4) in G of I */
   C := SOCentraliser (G, I, w, {f - 1, f, f + 1, f + 2});

   vprint User5: "Time to construct SO+4 as centraliser is  ", Cputime (t3);
   t3 := Cputime ();

   /* construct C = SO+(4) acting on {f - 1, f, f + 1, f + 2} */
   C := SOGoodCentraliser (G, C, 4, {1..f - 2} join {f + 3..d});
   vprint User5: "Time to get SO+4 action on factor is  ", Cputime (t3);

   /* set up Y = SO+(4) */
   Y := ExtractFactor (C, [f - 1..f + 2]);
   _ := InitialiseGroup (Y: generators := Y`UserGenerators, scalars:=false);

   assert MyIsSOPlusGroup (Y);

   t3 := Cputime ();
   vprint User5: "Composition Tree call for degree", Degree (Y);
   T := CompositionTree (Y: KernelRank := 10);
   g := SOPlusGlueElement (F);
   flag, wg := SolveWord (T, T[1], g);
   assert flag;

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
   E := SOChosenElements (G: Words := false);

   if d - f eq 3 then 
      word := (wg * W1[8]);
   else
      word := W2[4] * wg * W1[8];
   end if;

   W := [W2[i] : i in [1..3]] cat [word];
   
   return E, W;
   
end function;

/* recognize O(d, q) in its natural representation when q = 3 mod 4 */

SOSpecialProcess := function (G : Limit := 100, 
                    Special := false, SpecialGroup := true)

   _ := InitialiseGroup (G);
   d := Degree (G);
   F := BaseRing (G);
   q := #F;

   if d eq 5 then
      X, Y, CB := SolveO5 (G);
      return X, Y, CB;
   elif d eq 3 then 
      X, Y, CB := SOChosenElements (G: SpecialGroup := SpecialGroup);
      return X, Y, CB;
   end if;
      
   if d mod 4 eq 1 and q mod 4 eq 3 then 
      Range := [d - 5];
   else 
      Range := [d - 3];
   end if;
   g, w, H, b, CB, dim := SOSplitSpace (G: Range := Range,
                                           type := "orthogonalcircle");

   flag, form := SymmetricBilinearForm (G);
   assert flag;
   form := CB * form * Transpose (CB);

   vprint User5: "Now sort out new form";
   form := SOChangeForm (d, F, form);
   cb := SOFormBaseChange (G, form, dim: type := "orthogonalcircle");

   cb := cb^-1;
   H := H^(cb^-1);

   H`SLPGroup := G`SLPGroup;
   H`UserGenerators := [cb * CB * x * CB^-1 * cb^-1: x in UserGenerators (G)];
   H`SLPGroupHom := MyHom (H, H`SLPGroup, UserGenerators (H));

   C := SOCentraliser (H, b, w, [1..dim]:
               Partial := true, SpecialGroup := SpecialGroup);

   C1 := SOGoodCentraliser (G, C, dim, {dim + 1..d}); 

   C2 := SOGoodCentraliser (G, C, d - dim, {1..dim}: type := "orthogonalcircle");
   G1 := ExtractFactor (C1, {1..dim});
   G2 := ExtractFactor (C2, {dim + 1..d});

   flag, form1 := OrthogonalForm (G1);
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
         f1 := SpinorNorm (GL(Nrows (B[1]), F)!B[1], form1);
         f2 := SpinorNorm (GL(Nrows (B[2]), F)!B[2], form2);
         found := f1 eq 1 and f2 eq 1 and Determinant (B[1]) eq 1
               and Determinant (B[2]) eq 1;
      end if;
   until found or nmr gt Limit;

   if nmr gt Limit then
      C:Magma;
      error "Failed to find good element in SOSpecialProcess";
   end if;

   B := MatrixBlocks (C, x);
   w := w^(o div 2);
   w := FactorToParent (G, C, w);

   D1 := sub < GL(d, F) | C1, x>;
   D1`UserGenerators := C1`UserGenerators cat [x];
   D1`UserWords := C1`UserWords cat [w];
   D1`SLPGroup := SLPGroup (#D1`UserGenerators);
   D1`SLPGroupHom := MyHom (D1, D1`SLPGroup, UserGenerators (D1));
   C1 := D1;

   G1 := ExtractFactor (C1, {1..dim});

   vprint User5: "Call 1 SOSpecialProcess dimension of G1 is ", Degree (G1);
   E1, W1, CB1 := SOPlusProcess (G1, d: Special := Special,
                                        SpecialGroup := true);
   // assert Verify (G1, E1, W1, CB1); 

   /* pull back words to G */
   W1 := [FactorToParent (G, C1, W1[i]): i in [1..#W1]];

   rem := d - dim;
   h := H`SLPGroupHom (W1[#W1]);

   D2 := sub<GL(d, F) | C2, h>;
   D2`UserGenerators := C2`UserGenerators cat [h];
   D2`UserWords := C2`UserWords cat [W1[#W1]];
   D2`SLPGroup := SLPGroup (#D2`UserGenerators);
   D2`SLPGroupHom := MyHom (D2, D2`SLPGroup, UserGenerators (D2));
   C2 := D2;
   G2 := ExtractFactor (C2, {dim + 1..d});

   vprint User5: "Call 2 SOSpecialProcess dimension of G2 is ", Degree (G2);
   E2, W2, CB2 := SOProcess (G2, d: SpecialGroup := true, Special := Special);
   // assert Verify (G2, E2, W2, CB2); 
   W2 := [FactorToParent (G, C2, W2[i]): i in [1..#W2]];

   Total := CombineMatrices (CB1, CB2);
   H := ApplyCOB (G, Total * cb * CB);

   w := W2[#W2];

   vprint User5: "call SOSpecialGlue", Degree (G1), Degree (G2);
   X, Y := SOSpecialGlue (H, G1, E1, W1, G2, E2, W2); 
   // assert Verify (G,X,Y,Total * CB);

   return X, Y, Total * cb * CB;
end function;
