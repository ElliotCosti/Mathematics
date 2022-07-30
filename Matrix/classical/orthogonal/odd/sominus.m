forward MinusSpecialProcess;
forward SolveSixMinus;

/* if SpecialGroup is true, then standard generators
   for SO-, otherwise for Omega- */

MinusChosenElements := function (G: Words := true, SpecialGroup := false)

   n := Degree (G);
   assert IsEven (n) and n gt 2; 

   F := BaseRing (G);
   q := #F;

   w := PrimitiveElement (F);

   MA := MatrixAlgebra (F, n);
   A := MatrixAlgebra (F, 2);

   E<delta> := GF (q^2);
   mu := delta^((q + 1) div 2);

   MA := MatrixAlgebra (F, n);
   
   I := A![1,0,0,1];
 
   M := MatrixAlgebra (F, 4);

   a := A![1,1,0,1];
   b := A![2,0,0,0];
   c := A![0,1,0,0];
   d := A![1,0,0,1];
   U := Zero (MA);
   for i in [1..n - 4] do U[i][i] := 1; end for;
   InsertBlock (~U, a, n - 3, n - 3);
   InsertBlock (~U, b, n - 3, n - 1);
   InsertBlock (~U, c, n - 1, n - 3);
   InsertBlock (~U, d, n - 1, n - 1);
   U := Transpose (U);

   a := A![1,0,1,1];
   b := A![0,0,2,0];
   c := A![1,0,0,0];
   d := A![1,0,0,1];
   L := Zero (MA);
   for i in [1..n - 4] do L[i][i] := 1; end for;
   InsertBlock (~L, a, n - 3, n - 3);
   InsertBlock (~L, b, n - 3, n - 1);
   InsertBlock (~L, c, n - 1, n - 3);
   InsertBlock (~L, d, n - 1, n - 1);
   L := Transpose (L);

   a := A! [delta^(q + 1), 0, 0, delta^(-q - 1)]; 
   d := A![1/2 * (delta^(q - 1) + delta^(-q + 1)),
            1/2 * mu * (delta^(q - 1) - delta^(-q + 1)),
            1/2 * mu^(-1) * (delta^(q - 1) - delta^(-q + 1)),
            1/2 * (delta^(q - 1) + delta^(-q + 1))];
   D := Zero (MA);
   for i in [1..n - 4] do D[i][i] := 1; end for;
   InsertBlock (~D, a, n - 3, n - 3);
   InsertBlock (~D, d, n - 1, n - 1);

   Gens := [U, L, D];

   if n gt 4 then
      p := Zero (MA);
      InsertBlock (~p, I, 1, 3);
      InsertBlock (~p, -I, 3, 1);
      for i in [5..n] do p[i][i] := 1; end for;
      Append (~Gens, p);
   end if;

   if n gt 6 then 
      h := Zero (MA);
      m := n - 2;
      for i in [1..m div 2 - 1] do
         x := (i - 1) * 2 + 1;
         y := x + 2;
         InsertBlock (~h, I, x, y);
      end for;
      InsertBlock (~h, (-1)^(n div 2) * I, m - 1, 1);
      InsertBlock (~h, I, n - 1, n - 1);
      Append (~Gens, h);
   end if;

   if SpecialGroup then
      m := Identity (MA);
      if q mod 4 eq 3 then 
         m[1][1] := -1;
         m[2][2] := -1;
      else
         m[n-1][n-1] := -1;
         m[n][n] := -1;
      end if;
      Append (~Gens, m);
   end if;

   P := GL (n, q);

   _, cb := ConjugateToStandardCopy (G, "orthogonalminus");

   gens := [P!x: x in Gens];

   if Words then
      W := [];
      G`CentraliserTrees := [];
      T := CompositionTree (G: KernelRank := 10);
      for i in [1..#gens] do 
         flag, w := SolveWord (T, T[1], gens[i]^(cb^-1)); 
         if flag eq false then 
            G:Magma; "i = ", i;
            error "Error in MinusChosenElements"; 
         end if;
         Append (~W, w);
      end for;
      return gens, W, cb^-1;
   else
      return gens, cb^-1, _;
   end if;

end function;

/* if SpecialGroup is true, then standard generators
   for SO-, otherwise for Omega- */

MinusChosenElements := function (G: Words := true, SpecialGroup := false)

   n := Degree (G);
   assert IsEven (n) and n gt 2; 

   F := BaseRing (G);
   q := #F;

   w := PrimitiveElement (F);

   MA := MatrixAlgebra (F, n);
   A := MatrixAlgebra (F, 2);

   E<delta> := GF (q^2);
   mu := delta^((q + 1) div 2);

   MA := MatrixAlgebra (F, n);
   
   I := A![1,0,0,1];
 
   M := MatrixAlgebra (F, 4);

   a := A![1,1,0,1];
   b := A![2,0,0,0];
   c := A![0,1,0,0];
   d := A![1,0,0,1];

   U := Identity (MA);
   U[n-3][n-3] := 0; U[n-3][n-2] := 1;
   U[n-2][n-3] := 1; U[n-2][n-2] := 0;
   U[n-1][n-1] := -1;

   a := A![1,0,1,1];
   b := A![0,0,2,0];
   c := A![1,0,0,0];
   d := A![1,0,0,1];
   L := Zero (MA);
   for i in [1..n - 4] do L[i][i] := 1; end for;
   InsertBlock (~L, a, n - 3, n - 3);
   InsertBlock (~L, b, n - 3, n - 1);
   InsertBlock (~L, c, n - 1, n - 3);
   InsertBlock (~L, d, n - 1, n - 1);
   L := Transpose (L);

   a := A![delta^(q + 1), 0, 0, delta^(-q - 1)]; 
   d := A![1/2 * (delta^(q - 1) + delta^(-q + 1)),
           1/2 * mu * (delta^(q - 1) - delta^(-q + 1)),
           1/2 * mu^(-1) * (delta^(q - 1) - delta^(-q + 1)),
           1/2 * (delta^(q - 1) + delta^(-q + 1))];
   D := Zero (MA);
   for i in [1..n - 4] do D[i][i] := 1; end for;
   InsertBlock (~D, a, n - 3, n - 3);
   InsertBlock (~D, d, n - 1, n - 1);
   D := Transpose (D);

   Gens := [U, L, D];

   if n gt 4 then
      p := Zero (MA);
      InsertBlock (~p, I, 1, 3);
      InsertBlock (~p, -I, 3, 1);
      for i in [5..n] do p[i][i] := 1; end for;
      Append (~Gens, p);
   end if;

   if n gt 6 then 
      h := Zero (MA);
      m := n - 2;
      for i in [1..m div 2 - 1] do
         x := (i - 1) * 2 + 1;
         y := x + 2;
         InsertBlock (~h, I, x, y);
      end for;
      InsertBlock (~h, (-1)^(n div 2) * I, m - 1, 1);
      InsertBlock (~h, I, n - 1, n - 1);
      Append (~Gens, h);
   end if;

   if SpecialGroup then
      m := Identity (MA);
      if q mod 4 eq 3 then 
         m[1][1] := -1;
         m[2][2] := -1;
       else
         m[n-1][n-1] := -1;
         m[n][n] := -1;
       end if;
      Append (~Gens, m);
   end if;

   P := GL (n, q);

   _, cb := ConjugateToStandardCopy (G, "orthogonalminus");

   gens := [P!x: x in Gens];

   if Words then
      W := [];
      G`CentraliserTrees := [];
      T := CompositionTree (G: KernelRank := 10);
      for i in [1..#gens] do 
         flag, w := SolveWord (T, T[1], gens[i]^(cb^-1)); 
         if flag eq false then 
            G:Magma; "i = ", i;
            error "Error in MinusChosenElements"; 
         end if;
         Append (~W, w);
      end for;
      return gens, W, cb^-1;
   else
      return gens, cb^-1, _;
   end if;

end function;

/* g involution in G; wg is corresponding word; construct its centraliser 
   whose derived group is SO+(f, q) x SO-(d - f, q) */

MinusCentraliser := function (G, g, wg, action: 
   Partial := false, Words := true, fct := Order, SpecialGroup := false)

   S := G`SLPGroup;
   F := BaseRing (G);
   d := Degree (G); q := #F;

   if Type (action) eq SeqEnum then action := {x : x in action}; end if;
   rest := Sort (SetToSequence ({1..d} diff action));
   action := Sort ([x : x in action]);
   r := #action;

   lambda := UserGenerators (G)[1];
   E := [[lambda], [g]]; W := [[S.1], [wg]]; 

   flag := false;
   i := 3;  
   repeat 
      if Words then 
         e, w := SpecialGeneratorsWords (G, g, wg: fct := fct);
      else 
         e := BrayGenerators (G, g);
      end if;
      e1 := [];  w1 := [];
      for i in [1..#e] do 
         x := e[i];
         a := ExtractAction (x, action);
         b :=  ExtractAction (x, rest);
         e1 := []; w1 := [];
         if Determinant (a) eq 1 and Determinant (b) eq 1 then
            Append (~e1, x);
            if Words then Append (~w1, w[i]); end if;
         end if;
      end for;
      if #e1 gt 0 then 
         E[i]:= e1; if Words then W[i] := w1; end if;
         vprint User5: "Lengths are ", [#e: e in E];
         C := sub <GL(d, F) | &cat(E)>;
         S := Sections (C);
         vprint User5: "# of sections in result is now ", #S;
         if #S eq 1 then error "Problem in MinusCentraliser"; end if;
         flag := IsDirectProductOs (C, action: Partial := Partial, 
                 SpecialGroup := SpecialGroup, Plus := false);
         i +:= 1;
      end if;
   until flag;

   vprint User5: "Number of generators for centraliser is", Ngens (C);

   E := &cat(E);
   W := &cat(W);
   C`UserGenerators := E;
   if Words then C`UserWords := W; end if;

   B := SLPGroup (#E);
   C`SLPGroup := B;
   C`SLPGroupHom := MyHom (C, B, E);

   return C;

end function;

/* G group with basis which exhibits split as f, d - f;
   G1 is O+(f) as f x f matrices;
   E1, W1 are elements, words for O+(f);
   similarly G2, E2, W2 describe O-(d - f) */
   
SOMinusGlue := function (G, G1, E1, W1, G2, E2, W2: SpecialGroup := false)

   d := Degree (G);
   F := BaseRing (G); 
   q := #F;
   
   /* top piece */
   f := Degree (G1);

   /* construct u = Diagonal ([1, 1, ..., -1, -1]) */
   if q mod 4 eq 1 then 
      if f eq 2 then
         u := E1[3];
         o := Order (u);
         wu := W1[3];
         wu := wu^(o div 2);
      else
         pow := (q - 1) div 4;
         wa1 := W1[6];  wb1 := W1[3];  wp := W1[8];
         wu := (wa1 * wb1)^(pow); 
         wu := wu^(wp^-1);
      end if;
      /* construct v = Diagonal ([-1,-1, ..., 1, 1]) */
      wv := W2[3]^((q^2 - 1) div 4); 
   else 
      assert SpecialGroup; 
      wu := W1[#W1]; wp := W1[8];
      wu := wu^(wp^-1);
      wv := W2[#W2];
   end if;

   /* w is word for 
      uv = Diagonal ([1, 1, ..., -1, -1, -1,-1, 1, 1, ..., 1])
      where -1s are in position f - 1, ..,f + 2 */
   w := wu * wv;

   /* set up matrix I for uv */
   M := MatrixAlgebra (F, d);
   I := Identity (M);
   for i in [f - 1..f + 2] do I[i][i] := -1; end for;
   I := GL(d, F) ! I;
 
/* 
"SOMinus NOW COMPUT ";
JJ := G`SLPGroupHom (w);
"compute  is ", JJ;
assert I eq JJ;
*/

   t3 := Cputime ();
   /* construct centraliser SO+(4) x SO-(d - 4) in G of I */
   C := MinusCentraliser (G, I, w, {f - 1, f, f + 1, f + 2}: 
             SpecialGroup := SpecialGroup);

   vprint User5: "Time to construct SO+4 as centraliser is  ", Cputime (t3);

   /* construct C = SO+(4) acting on {f - 1, f, f + 1, f + 2} */
   C := SOGoodCentraliser (G, C, 4, {1..f - 2} join {f + 3..d}: 
                         SpecialGroup := SpecialGroup);
   vprint User5: "Time to get SO+4 action on factor is  ", Cputime (t3);

   /* set up Y = SO+(4) */
   Y := ExtractFactor (C, [f - 1..f + 2]);
   _ := InitialiseGroup (Y: generators := Y`UserGenerators, scalars:=false);
   if MyIsSOPlusGroup (Y) eq false then
      Y:Magma; error "3 Group not SO+4";
   end if;

   vprint User5: "Composition Tree call for degree", Degree (Y);
   T := CompositionTree (Y: KernelRank := 10);
   g := SOPlusGlueElement (F);
   flag, wg := SolveWord (T, T[1], g);

   /* C to G */
   T := G`SLPGroup;
   gamma := hom <C`SLPGroup -> T | C`UserWords cat [wu]>;
   vprint User5: "Total time in Composition Tree is ", Cputime (t3);

   /* SO+4 to C */
   wg := ImagesOfWords (Y, C, [wg]);
   wg := wg[1];

   /* C to G */
   T := G`SLPGroup;
   gamma := hom < C`SLPGroup -> T | C`UserWords cat [wu]>;
   wg := gamma (wg);

   /* set up basis elements and words for G */
   E := MinusChosenElements (G: Words := false, SpecialGroup := SpecialGroup);

   word := (wg * W1[8]);
   
   if SpecialGroup then o := Order (E1[#E1]); o := o div 2; end if;
   W := W2;
   if f eq 2 then 
      W[4] := word;
   elif d - f in [4] then 
      W[4] := W1[4];
      W[5] := word;
   end if;

   if SpecialGroup then 
      if q mod 4 eq 3 then W[#W + 1] := W1[#W1]^o; 
      else W[#W + 1] := W2[#W2]; end if;
   end if;

   return E, W;

end function;

MinusProcess := function (G, InputDimension: SpecialGroup :=false, 
                          Scalars := false, Special := false)

   _ := InitialiseGroup (G: scalars := Scalars, generators := UserGenerators (G));
   d := Degree (G);
   F := BaseRing (G);
   q := #F;

   if (d eq 4) or (d le 8 and q eq 3) then
      vprint User5: "Call CompositionTree for degree ", d;
      X, Y, CB := MinusChosenElements (G : SpecialGroup := SpecialGroup);
      return X, Y, CB;
   end if;

   if (not SpecialGroup) and Degree (G) eq 6 and q mod 4 eq 3 then 
      X, Y, CB := SolveSixMinus (G);
      return X, Y, CB;
   end if;

   Range := [d - 4];
   g, w, H, b, CB, dim := SOSplitSpace (G: SpecialGroup := SpecialGroup, 
                          type := "orthogonalminus", Range := Range);

   vprint User5: "Now sort out new form";
   flag, form := SymmetricBilinearForm (G);
   assert flag;
   form := CB * form * Transpose (CB);

   cb := SOFormBaseChange (G, form, dim: type := "orthogonalminus");
   cb := cb^-1;
   H := H^(cb^-1);

   H`SLPGroup := G`SLPGroup;
   H`UserGenerators := [cb * CB * x * CB^-1 * cb^-1: x in UserGenerators (G)];
   H`SLPGroupHom := MyHom (H, H`SLPGroup, UserGenerators (H));

   C := MinusCentraliser (H, b, w, [1..dim]: SpecialGroup := SpecialGroup);

"here 1";
time   C1 := SOGoodCentraliser (G, C, dim, {dim + 1..d}: SpecialGroup:=SpecialGroup);
"here 2";
time   C2 := SOGoodCentraliser (G, C, d - dim, {1..dim}: 
            type := "minus", SpecialGroup := SpecialGroup);
"back 2";

   G1 := ExtractFactor (C1, {1..dim});
   G2 := ExtractFactor (C2, {dim + 1..d});

   vprint User5: "SOMinus call 1 dimension of G1 is ", Degree (G1);
   E1, W1, CB1 := SOPlusProcess(G1, d: SpecialGroup := SpecialGroup);
   // assert Verify (G1, E1, W1, CB1); 

   /* pull back words to G */
   W1 := [FactorToParent (G, C1, W1[i]): i in [1..#W1]];
   
   vprint User5: "SOMinus call 2 dimension of G2 is ", Degree (G2);
   E2, W2, CB2 := $$ (G2, InputDimension: 
                      SpecialGroup := SpecialGroup, Special := Special);
   // assert Verify (G2, E2, W2, CB2); 
   W2 := [FactorToParent (G, C2, W2[i]): i in [1..#W2]];

   Total := CombineMatrices (CB1, CB2);
   H := ApplyCOB (G, Total * cb * CB);

   vprint User5: "Call SOMinusGlue", Degree (G1), Degree (G2);

   t1 := Cputime ();
   X, Y := SOMinusGlue (H, G1, E1, W1, G2, E2, W2: SpecialGroup := SpecialGroup);
   // assert Verify (G,X,Y,Total * CB);
   vprint User5: "Time to glue in SOMinus is ", Cputime (t1);
   return X, Y, Total * cb * CB;
end function;

/* construct Steinberg generators of G */

SolveOMinus := function (G: Special := false)
   d := Degree (G);
   F := BaseRing (G);
   q := #F;
   if (d gt 8 and q eq 3) or (d gt 4 and q gt 3 and q mod 4 eq 3) then
      E, W, CB := MinusSpecialProcess (G: Special := Special,
                              SpecialGroup := true);
   else
      E, W, CB := MinusProcess (G, d: Scalars := true, Special := Special,
                           SpecialGroup := false);
   end if;
   return E, W, CB;
end function;

SolveSOMinus := function (G: Special := false)
   d := Degree (G);
   E, W, CB := MinusProcess (G, d: Scalars := true, 
                 Special := Special, SpecialGroup := true);
   return E, W, CB;
end function;
