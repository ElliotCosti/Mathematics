forward SOPlusSpecialProcess;

SOFormBaseChange := function (G, form, dim: type := "orthogonalplus")

   F := BaseRing (G);
   q := #F;
   d := Degree (G);
   a := ExtractBlock (form, 1, 1, dim, dim);
   op := StandardOPlusForm (dim, q);
   x := TransformForm (a, "orthogonalplus");
   y := TransformForm (op, "orthogonalplus");
   a := x * y^-1;

   b := ExtractBlock (form, dim + 1, dim + 1, d - dim, d - dim);

   if type eq "orthogonalplus" then 
      om := StandardOPlusForm (d - dim, q);
   elif type eq "orthogonalminus" then 
      om := StandardOMinusForm (d - dim, q);
   elif type eq "orthogonalcircle" then 
      om := StandardOForm (d - dim, q);
   else
      error "Error in SOFormBaseChange";
   end if;

   x := TransformForm (b, type);
   y := TransformForm (om, type);
   b := x * y^-1;
   
   A := DiagonalJoin (a, b);
   return GL(d, F)!A;

end function;

/* g involution in G; wg is corresponding word; construct its centraliser 
   whose derived group is SO+(f, q) x SO+(d - f, q) */

SOCentraliser := function (G, g, wg, action: MinGens := 2,
        Limit := 1000, Partial := false, Words := true, 
        fct := Order, SpecialGroup := false)

   if Words then S := G`SLPGroup; end if;
   F := BaseRing (G);
   d := Degree (G); q := #F;

   if Type (action) eq SeqEnum then action := {x : x in action}; end if;
   rest := Sort (SetToSequence ({1..d} diff action));
   action := Sort ([x : x in action]);
   r := #action;

   if Words then 
      lambda := UserGenerators (G)[1];
      E := [[lambda], [g]]; if Words then W := [[S.1], [wg]]; end if;
   else 
      E := [[g], [g]];
   end if;

   flag := false; 

   /* O+(4, 3) is soluble and we don't construct
      as normal closure of every 2-generator subgroup; 
      also problems constructing O+4 x O+4 */

   if r eq 2 then MinGens := 50; end if;
   if (d eq 4 and q eq 3) or (d eq 6) or (d eq 8 and r eq 4) then 
       MinGens := Maximum (MinGens, 8); 
   end if;         

   i := 3; nmr := 0;  
   repeat 
       nmr +:= 1;
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
         flag := IsDirectProductOs (C, action: 
                 Partial := Partial, SpecialGroup := SpecialGroup);
         i +:= 1;
      end if;
   until (nmr gt Limit) or (flag and Ngens (C) gt MinGens);

   if nmr gt Limit then
      error "Failed in SOCentraliser";
   end if;

   vprint User5: "Number of generators needed for centraliser is", Ngens (C);

   E := &cat(E);
   C`UserGenerators := E;
   if Words then 
      W := &cat(W); C`UserWords := W; 
   end if;

   B := SLPGroup (#E);
   C`SLPGroup := B;
   C`SLPGroupHom := MyHom (C, B, E);

   return C;

end function;

/* G has degree 4k; find involution to split space into I_2k and -I_2k */

SOSplitInvolution := function (G: Required := Degree (G) div 2, 
                                Scalars := false)

    _ := InitialiseGroup (G: scalars := Scalars, 
                             generators := UserGenerators (G));
   d := Degree (G);

   F := BaseRing (G);
   e := Required;

   if (Degree (G) le 8)  then 
      Range := [Required];
      "Search for precisely", Range;
   else 
      Range := [Degree(G) div 3..2 * Degree(G) div 3];
      "Search for ", Range;
   end if;

   if not (Required in Range) then
      Range cat:= [Maximum (Range) + 1 ..Required];
      "Amended -- Search for ", Range;
   end if;

   g, w, H, b, CB, dim, minus := SOSplitSpace (G: Range := Range, 
                                             SortSpaces := false);
   plus := dim;

   if e eq minus then 
      found := true;
      return g, w, b, CB;
   end if;

   H`SLPGroup := G`SLPGroup;
   H`UserGenerators := [CB * x * CB^-1: x in UserGenerators (G)];
   H`SLPGroupHom := MyHom (H, H`SLPGroup, UserGenerators (H));

   C := SOCentraliser (H, b, w, [1..dim]);

   MA := MatrixAlgebra (F, d);
   Large := Identity (MA);
   B := Identity (MA);

   pullback := true;

   if e le Minimum ([minus, plus]) then 
      if minus lt plus then 
         C1 := SOGoodCentraliser (G, C, minus, {1..dim});
         G1 := ExtractFactor (C1, {dim + 1..d});
      else 
         C1 := SOGoodCentraliser (G, C, plus, {plus + 1..d});
         G1 := ExtractFactor (C1, {1..dim});
      end if;
      g, w, smallb, SmallCB := $$ (G1: Scalars := false, Required := e);
      pos := minus lt plus select plus else 0;
      InsertBlock (~Large, SmallCB, pos + 1, pos + 1);
      InsertBlock (~B, smallb, pos + 1, pos + 1);
   elif e gt minus and e le plus then 
      C1 := SOGoodCentraliser (G, C, plus, {plus + 1..d});
      G1 := ExtractFactor (C1, {1..dim});
      g, w, smallb, SmallCB := $$ (G1: Scalars := false, Required := e);
      InsertBlock (~Large, SmallCB, 1, 1);
      InsertBlock (~B, smallb, 1, 1);
   elif e gt plus and e le minus then 
      C1 := SOGoodCentraliser (G, C, minus, {1..dim});
      G1 := ExtractFactor (C1, {dim + 1..d});
      g, w, smallb, SmallCB := $$ (G1: Scalars := false, Required := e);
      InsertBlock (~Large, SmallCB, plus + 1, plus + 1);
      InsertBlock (~B, smallb, plus + 1, plus + 1);
   elif e gt plus and e gt minus then 
      C1 := SOGoodCentraliser (G, C, plus, {plus + 1..d});
      G1 := ExtractFactor (C1, {1..dim});
      g1, w1, smallb1, SmallCB1 := $$ (G1: Scalars := false, Required := e - minus);
      /* pull back words to G */
      w1 := FactorToParent (G, C1, w1);
      w := w * w1;
      InsertBlock (~Large, SmallCB1, 1, 1);
      InsertBlock (~B, smallb1, 1, 1);
      CB := Large * CB;
      b := b * B;
      pullback := false;
  else
     error "should not be here";
  end if;
     
   /* pull back words to G */
   if pullback then 
      CB := Large * CB;
      b := B;
      w := FactorToParent (G, C1, w);
   end if;

   return g, w, b, CB;
end function;

/* G has degree 4k; find involution [I_2k, -I_2k] */

SOSpecialSplitSpace := function (G)

   g, w, b, cb := SOSplitInvolution (G);

   d := Degree (G);
   F := BaseRing (G);

   g := GL(d, F) ! (cb^-1 * b * cb);

   U := Eigenspace (g, 1);
   W := Eigenspace (g, -1);

   /* if even, ensure large space is at top */
   if IsEven (d) and Dimension (W) gt Dimension (U) then 
      tmp := U; U := W; W := tmp;
   end if;

   b, H, CB := BasisOfInvolution (G, g, U, W);

   return g, w, H, b, CB, Dimension (U);

end function;

/* if SpecialGroup is true, then standard generators
   for SO+, otherwise for Omega+ */

PlusChosenElements := function (G: Words := true, SpecialGroup := false)

   n := Degree (G);
   F := BaseRing (G);
   q := #F;

   w := PrimitiveElement (F);
   A := MatrixAlgebra (F, 2);

   if n eq 2 then 
      Gens := [Identity (A): i in [1..8]];
      flag := exists (x){x : x in Generators (G) | IsEven (Order (x))};
      assert flag;
      if flag then Gens[3] := x; end if;
      if SpecialGroup then 
         Gens[#Gens + 1] := -Identity (GL(2, F)); 
      end if;
   else 
      MA := MatrixAlgebra (F, n);
      M := MatrixAlgebra (F, 4);

      s := Zero (MA);
      for i in [5..n] do s[i][i] := 1; end for;
      s[1][4] := -1; s[2][3] := -1; s[3][2] := 1; s[4][1] := 1;

      t4 := M![1,0,0,-1, 0,1,0,0, 0,1,1,0, 0,0,0,1];
      t := Identity (MA);
      InsertBlock (~t, t4, 1, 1);

      delta4 := DiagonalMatrix (F, [w, w^-1, w, w^-1]);
      delta := Identity (MA);
      InsertBlock (~delta, delta4, 1, 1);
      
      s1 := Zero (MA);
      for i in [5..n] do s1[i][i] := 1; end for;
      s1[1][3] := 1; s1[2][4] := 1; s1[3][1] := -1; s1[4][2] := -1;

      t4 := M![1,0,1,0,  0,1,0,0, 0,0,1,0, 0,-1,0,1];
      t1 := Identity (MA);
      InsertBlock (~t1, t4, 1, 1);

      delta4 := DiagonalMatrix (F, [w, w^-1, w^-1, w]);
      delta1 := Identity (MA);
      InsertBlock (~delta1, delta4, 1, 1);
      
      u := Identity (MA);

      I := Identity (A);
      v := Zero (MA);
      for i in [1..n div 2 - 1] do
         x := (i - 1) * 2 + 1;
         y := x + 2;
         InsertBlock (~v, I, x, y);
      end for;
      InsertBlock (~v, (-1)^(n div 2 + 1) * I, n - 1, 1);
      Gens := [s, t, delta, s1, t1, delta1, u, v];
      if SpecialGroup then 
         a :=  Identity (MA);
         _, b := Valuation (q - 1, 2);
         a[1][1] := w^b;
         a[2][2] := w^-b;
         Append (~Gens, a);
      end if;
   end if;

   if Degree (G) gt 2 then 
      _, cb := ConjugateToStandardCopy (G, "orthogonalplus");
   else
      cb := Identity (G);
   end if;

   P := GL (n, F);
   gens := [P!x: x in Gens];

   if Words then
      W := [];
      G`CentraliserTrees := [];
      T := CompositionTree (G: KernelRank := 10);
      for i in [1..#gens] do 
         flag, w := SolveWord (T, T[1], gens[i]^(cb^-1)); 
         if flag eq false then G:Magma; i; 
            error "Error in PlusChosenElements"; 
         end if;
         Append (~W, w);
      end for;
      return gens, W, cb^-1;
   else
      return gens, cb^-1, _;
   end if;

end function;

/* element to link first SO+ to second SO+ */

SOPlusGlueElement := function (F)

   M := MatrixAlgebra (F, 4);
   I := Zero (M);
   I[1][3] := 1;
   I[2][4] := 1;
   sign := -1;
   I[3][1] := sign * 1;
   I[4][2] := sign * 1;
   I := GL (4, F)!I;
   return I;
end function;

/* G group with basis which exhibits split as f, d - f;
   G1 is O+(f) as f x f matrices;
   E1, W1 are elements, words for O+(f);
   similarly G2, E2, W2 describe O+(d - f) */
   
SOPlusGlue := function (G, G1, E1, W1, G2, E2, W2: SpecialGroup := false)

   d := Degree (G);
   F := BaseRing (G); 
   q := #F;
   
   /* top piece */
   f := Degree (G1);

   if SpecialGroup then 
      wu := W1[#W1]; wp := W1[8];
      wu := wu^(wp^-1);
      wv := W2[#W2];
      if q mod 4 eq 1 then
         a, b := Valuation (q - 1, 2);
         o := (q - 1) div (b);
         wu := wu^(o div 2);
         if Degree (G2) gt 2 then 
            wv := wv^(o div 2);
         end if;
      end if;
      if Degree (G2) eq 2 then 
         b := E2[#E2];
         wv := wv^(Order (b) div 2);
      end if;
   else 
      /* construct u = Diagonal ([1, 1, ..., -1, -1]) */
      pow := (q - 1) div 4;
      wa1 := W1[6]; wb1 := W1[3]; wp := W1[8];
      wu := (wa1 * wb1)^(pow); 
      wu := wu^(wp^-1);

      /* construct v = Diagonal ([-1,-1, ..., 1, 1]) */
      if d - f gt 2 then 
         wa2 := W2[6]; wb2 := W2[3]; 
         wv := (wa2 * wb2)^(pow);
      else
         b := E2[3];
         o := Order (b);
         wv := W2[3]^(o div 2);
      end if;
   end if;

   /* w is word for 
      uv = Diagonal ([ 1, 1, ..., -1, -1, -1,-1, 1, 1, ..., 1])
      where -1s are in position f - 1, ..,f + 2 */
   w := wu * wv;

   /* set up matrix I for uv */
   M := MatrixAlgebra (F, d);
   I := Identity (M);
   for i in [f - 1..f + 2] do I[i][i] := -1; end for;
   I := GL(d, F) ! I;
 
/* 
"NOW COMPUT ";
time JJ := G`SLPGroupHom (w);
"Result is ", JJ;
assert I eq  JJ;
*/

   t3 := Cputime ();
   /* construct centraliser SO+(4) x SO+(d - 4) in G of I */
   C := SOCentraliser (G, I, w, {f - 1, f, f + 1, f + 2}: 
                                 SpecialGroup := SpecialGroup);

   vprint User5: "Time to construct SO+4 as centraliser is  ", Cputime (t3);

   /* construct C = SO+(4) acting on {f - 1, f, f + 1, f + 2} */
   C := SOGoodCentraliser (G, C, 4, {1..f - 2} join {f + 3..d}: 
                         SpecialGroup := SpecialGroup);
   vprint User5: "Time to get SO+4 action on factor is  ", Cputime (t3);

   /* set up Y = SO+(4) */
   Y := ExtractFactor (C, [f - 1..f + 2]);
   _ := InitialiseGroup (Y: generators := Y`UserGenerators, scalars:=false);

   vprint User5: "Composition Tree call for degree", Degree (Y);
   T := CompositionTree (Y: KernelRank := 10);
   g := SOPlusGlueElement (F);
   flag, wg := SolveWord (T, T[1], g);

   /* C to G */
   T := G`SLPGroup;
   gamma := hom <C`SLPGroup -> T | C`UserWords cat [wu]>;
   vprint User5: "Total Time in Composition Tree is ", Cputime (t3);

   /* SO+4 to C */
   wg := ImagesOfWords (Y, C, [wg]);
   wg := wg[1];

   /* C to G */
   T := G`SLPGroup;
   gamma := hom <C`SLPGroup -> T | C`UserWords cat [wu]>;
   wg := gamma (wg);

   /* set up basis elements and words for G */
   E := PlusChosenElements (G: Words := false, SpecialGroup := SpecialGroup);

   word := (W2[8] * wg * W1[8]);

   W1[8] := word;

   return E, W1;

end function;

/* recognize O+ in its natural representation */

SOPlusProcess := function (G, InputDimension: SpecialGroup :=false, 
                 Partial := false,  Scalars := false, Special := false)

   _ := InitialiseGroup (G: scalars := Scalars, generators := UserGenerators (G));

   d := Degree (G);
   F := BaseRing (G);
   q := #F;

   if (d le 4) or (d le 8 and q eq 3) then 
      vprint User5: "Call CompositionTree for degree ", d;
      X, Y, CB := PlusChosenElements (G : SpecialGroup := SpecialGroup);
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
      vprint User5: "Range is ", Range;
      if Degree (G) eq 4 then Range := [2]; end if;
      g, w, H, b, CB, dim := SOSplitSpace (G: Range := Range);
   end if;

   vprint User5: "Now sort out new form";
   flag, form := SymmetricBilinearForm (G);
   assert flag;

   form := CB * form * Transpose (CB);
   cb := SOFormBaseChange (G, form, dim: type := "orthogonalplus");

   cb := cb^-1;
   H := H^(cb^-1);

   H`SLPGroup := G`SLPGroup;
   H`UserGenerators := [cb * CB * x * CB^-1 * cb^-1: x in UserGenerators (G)];
   H`SLPGroupHom := MyHom (H, H`SLPGroup, UserGenerators (H));

   found := true; trial := 5; MinGens := 2; offset := 6;
   repeat 
      trial -:= 1;
      if (d eq 8 and dim eq 4) or (d eq 6) then MinGens +:= offset; end if;
      C := SOCentraliser (H, b, w, [1..dim]: Partial := Partial,
                MinGens := MinGens, SpecialGroup := SpecialGroup);

      C1 := SOGoodCentraliser (G, C, dim, {dim + 1..d}: 
                             SpecialGroup := SpecialGroup);
      if d eq 8 and dim eq 4 then
         found := not (C1 cmpeq false);
      elif C1 cmpeq BoolElt then 
         error "Failed to construct subgroup";  C:Magma; 
      end if;

      if found then 
         C2 := SOGoodCentraliser (G, C, d - dim, {1..dim}: 
                                SpecialGroup := SpecialGroup);
         if (d eq 8 and dim eq 4) or (d eq 6) then
            found := not (C2 cmpeq false);
         elif C2 cmpeq BoolElt then 
            error "Failed to construct subgroup";  C:Magma; 
         end if;
      end if;
   until found or trial eq 0;

   if not found or trial eq 0 then 
      C:Magma; 
      error "Failed to construct 2 centralisers"; 
   end if;

   G1 := ExtractFactor (C1, {1..dim});
   G2 := ExtractFactor (C2, {dim + 1..d});

   vprint User5: "Call 1 SOPlus Dimension of G1 is ", Degree (G1);
   E1, W1, CB1 := $$ (G1, InputDimension: Special := Special, 
                                          SpecialGroup := SpecialGroup);
   // assert Verify (G1, E1, W1, CB1); 

   /* pull back words to G */
   W1 := [FactorToParent (G, C1, W1[i]): i in [1..#W1]];
   
   /* if special we can conjugate solution for G1 under element 
      of projective centraliser to obtain solution for G2 */

   if Special and (Degree (G) mod 4 eq 0) then 
      "Search for projective generator";
      time theta, wtheta := ProjectiveGenerator (G, g, w);
      theta := cb * CB * theta * CB^-1 * cb^-1;
      /* now conjugate */
      W2 := [w^wtheta: w in W1]; 
      E2 := E1;
      LCB1 := CombineMatrices (CB1, CB1^0);
      B2 := [LCB1[i] : i in [1..dim]] cat [LCB1[i] * theta : i in [1..dim]];
      LCB2 := GL(d, F) ! &cat [Eltseq (b2): b2 in B2];
      CB2 := ExtractBlock (LCB2, dim + 1, dim + 1, dim, dim);
   else 
      vprint User5: "Call 2 SOPlus Dimension of G2 is ", Degree (G2);
      E2, W2, CB2 := $$ (G2, InputDimension: 
                         SpecialGroup := SpecialGroup, Special := Special);
      // assert Verify (G2, E2, W2, CB2); 
      W2 := [FactorToParent (G, C2, W2[i]): i in [1..#W2]];
   end if;

   Total := CombineMatrices (CB1, CB2);
   H := ApplyCOB (G, Total * cb * CB);

   t1 := Cputime ();
   vprint User5: "Call SOPlus Glue", Degree (G1), Degree (G2);

   X, Y := SOPlusGlue (H, G1, E1, W1, G2, E2, W2: SpecialGroup := SpecialGroup);
   // assert Verify (G,X,Y,Total * CB);

   vprint User5: "Time to SOPlus Glue is ", Cputime (t1);
   return X, Y, Total * cb * CB;
end function;

/* construct Steinberg generators of G */

SolveOPlus := function (G: Special := false)
   d := Degree (G);
   F := BaseRing (G);
   q := #F;
   if (d gt 8 and q eq 3) or (d gt 4 and q gt 3 and q mod 4 eq 3) then 
      E, W, CB := SOPlusSpecialProcess (G: Special := Special, 
                              SpecialGroup := true);
   else 
      E, W, CB := SOPlusProcess (G, d: Scalars := true, Special := Special, 
                           SpecialGroup := false);
   end if;
   return E, W, CB;
end function;

SolveSOPlus := function (G: Special := false)
   d := Degree (G);
   F := BaseRing (G);
   E, W, CB := SOPlusProcess (G, d: Special := Special, Scalars := true, 
                              SpecialGroup := true);
   return E, W, CB;
end function;
