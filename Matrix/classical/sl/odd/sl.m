SetVerbose ("User1",0);
// SetVerbose ("User5",1);

/* construct SL2 x SL2 in GL2 wr C2 */

ConstructSL2xSL2 := function (G)

   d := Degree (G);
   F := BaseRing (G);
   repeat 
      g, wg := RandomWord (G);
   until not InBaseGroup (g); 

   /* find element t = [b 0; 0 b^-1] where b is the 
     determinant of 2 x 2 block and b is primitive */

   E := [ GL(d, F) | ]; W := []; found := false;
   repeat 
      repeat 
         h, wh := RandomWord (G);
      until InBaseGroup (h) eq false;
      product := g * h;
      wp := wg * wh;
      Append (~E, product);
      Append (~W, wp);
      t := &*E;
      flag, A, B := InBaseGroup (t);
      if flag then w := Determinant (A); flag := IsPrimitive (w); end if;
   until flag;
   vprint User5: "Number of trials to find primitive element is ", #E;
   wt := &*W;

   /* find wreathing element [0, a^-1 : a 0] where
      a is determinant of 2 x 2 block and has value 1 */

   K := sub < F | w>;

   a := ExtractBlock (g, 1, 3, 2, 2);
   if Degree (F) eq 1 then 
      k := Log (w, Determinant (a));
   else 
      k := Log (K!Determinant (a));
   end if;
   tt := t^k;
   wtt := wt^k;
   b1 := g * tt;
   wb1 := wg * wtt;
   a := ExtractBlock (b1, 1, 3, 2, 2);
   assert Determinant (a) eq 1;

   /* get generators for SL(2, q) x SL(2, q) */
   E := [GL(d, F) | ]; W := [];
   repeat 
      repeat 
         h, wh := RandomWord (G);
      until InBaseGroup (h) eq false;
      product := g * h;
      wp := wg * wh;
      flag, A, B := InBaseGroup (product);
      det := Determinant (A); 
      if Degree (F) eq 1 then 
         k := Log (w, Determinant (a));
      else 
         k := Log (K!Determinant (a));
      end if;
      tt := t^k;
      wtt := wt^k;
      b2 :=  product * tt;
      wb2 := wp * wtt;
      Append (~E, b2);
      Append (~W, wb2);
      H := sub <GL(4, F) | E>;
      S := Sections (H);
      if #S eq 2 and forall{s : s in S | MyIsLinearGroup (s)} then
         U1 := S[1]`UserGenerators;
         U2 := S[2]`UserGenerators;
         flag := [ProjectiveOrder (x): x in U1] ne
                 [ProjectiveOrder (x): x in U2];
      else flag := false;
      end if;
   until flag;
   
   assert forall{i: i in [1..Ngens (H)] | Determinant (H.i) eq 1};
   return H, E, W, b1, wb1;
end function;

/* canonical basis for SL(d, q) */

SLChosenElements := function (G : Words := true)

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
   if d eq 3 then b := b^-1; end if;
 
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
      flag, wa := SolveWord (T, T[1], a); 
      if not flag  then G:Magma; error "Problem in SLChosenElements";  end if;
      flag, wb := SolveWord (T, T[1], b); 
      if not flag  then G:Magma; error "Problem in SLChosenElements"; end if;
      flag, wt := SolveWord (T, T[1], t); 
      if not flag  then G:Magma; error "Problem in SLChosenElements"; end if;
      flag, wdelta := SolveWord (T, T[1], delta); 
      if not flag  then G:Magma; error "Problem in SLChosenElements"; end if;
      return [a, b, t, delta], [wa, wb, wt, wdelta];
   else 
      return [a, b, t, delta], _;
   end if;
 
end function;

/* additional element for even degree case to give Sym (n) */

SLAdditionalElement := function (F)
   M := MatrixAlgebra (F, 4);
   I := Zero (M);
   I[1][2] := 1;
   I[2][3] := 1;
   I[3][4] := 1;
   I[4][1] := -1;
   I := GL (4, F)!I;
   return I;
end function;

/* given n-cycle mapping 1 to 2 described by B, use it to write 
   down change of basis so that resulting matrix is desired n-cycle
    (1, d, -(d- 1), -(d-2), ..., -2) */

SLNewBasis := function (H, B)
   F := BaseRing (H);
   d := Degree (H);
   V := VectorSpace (F, d);

   depth := [Depth (B[i]): i in [1..Nrows (B)]];
   Sign := [];
   for i in [1..#depth] do 
      Sign[i] := B[i][depth[i]] eq 1 select 1 else -1; 
   end for;

   D := [Sign[i] * depth[i] : i in [1..#depth]];

   X := [];
   previous := 1;
   for i in [1..d] do 
      X[i] := previous;
      if previous gt 0 then 
         previous := -D[previous]; 
      else 
         previous := D[-previous];
      end if;
   end for;

   Y := [];
   for i in [1..d] do 
      if X[i] gt 0 then 
         Y[i] := V.X[i];
      else 
         Y[i] := -V.-X[i];
      end if;
   end for;
   N := &cat [Eltseq (v): v in Y];
   return GL(d, F) ! N;
end function;

/* G group with basis which exhibits split as f, d - f;
   G1 is SL(f) as f x f matrices;
   E1, W1 are elements, words for SL(f);
   if d is even then E1[2] = (1,3,5,...,f - 1) (2,4,6,...,f);
   similarly G2, E2, W2 describe SL(d - f);
   if FinalCall is true then this is the final glue 
   and we must obtain additional element to give d-cycle */
   
SLGlue := function (G, G1, E1, W1, G2, E2, W2: FinalCall := false)

   d := Degree (G);
   F := BaseRing (G); 
   q := #F;
   
   a := E1[1]; b1 := E1[2]; t := E1[3]; 
   wb1 := W1[2];
   
   /* top piece */
   f := Degree (G1);

   /* construct u = Diagonal ([-1, -1, 1, ..., 1]) */
   o := q - 1;
   // delta := E1[4]; u := delta^(o div 2); 
   wdelta := W1[4]; wu := wdelta^(o div 2); 

   /* construct v = Diagonal ([1, ... 1, -1, -1]) */

   // if d is even then E2[2] = (1,3,5,...,d - 1) (2,4,6,...,d)
   b2 := E2[2]; wb2 := W2[2];
   // n := Nrows (b2) div 2 - 1;
   // delta := E2[4]; v := delta^(o div 2); v := v^(b2^-1);
   wdelta := W2[4]; wv := wdelta^(o div 2); wv := wv^(wb2^-1);

   /* w is word for 
      uv = Diagonal ([ -1, -1, 1, ..., 1, -1, 1])
      where -1s are in position 1, 2, d - 1, d */
   w := wu * wv;

   /* set up matrix I for uv */
   M := MatrixAlgebra (F, d);
   I := Identity (M);
   for i in [1, 2, d - 1, d] do I[i][i] := -1; end for;
   I := GL(d, F) ! I;

// "NOW COMPUT ";
// time JJ := G`SLPGroupHom (w);
// assert I eq  JJ;

   H := G;
t3 := Cputime ();
   /* construct centraliser GL(4) x GL(d - 4) in G of I */
   C := SecondSpecialCentraliser (G, I, w, {1, 2, d - 1, d}: 
                                  IsCorrectType := MyIsLinearGroup);
   vprint User5: "Time to construct SL4 as centraliser is  ", Cputime (t3);

   /* construct C = SL(4) acting on {1, 2, d - 1, d} */
   C := GoodCentraliser (G, C, 4, {3..d - 2});
   vprint User5: "Time to get SL4 action on factor is  ", Cputime (t3);

   /* modify C to include u as generator */
   MA := MatrixAlgebra (F, d);
   u := Identity (MA);
   for i in [1..2] do u[i][i] := -1; end for;

   C := RedefineGroup (G, C, u, wu);

   /* set up Y = SL(4) */
   Y := ExtractFactor (C, [1, 2, d - 1, d]);
   _ := InitialiseGroup (Y: generators := Y`UserGenerators, scalars:=false);
assert IsLinearGroup (Y);

   q := #F;

   if (not FinalCall) and (q ne 3) then

      vprint User5: "We are in SL2 call";

      /* construct projective centraliser of Diagonal ([-1, -1, 1, 1])
         in SL4; this is GL2 wr C2 */
      t3 := Cputime ();
      n := #Y`UserGenerators;
      m := Ngens (Y); 
      Cu := ThirdCentraliser (Y, Y.m, Y`SLPGroup.n); 
      vprint User5: "time to get GL2 wr C2 centraliser is ", Cputime (t3);

      t3 := Cputime ();
      /* find SL2 x SL2 as subgroup of GL2 wr C2; also obtain
         wreathing element x for SL2 wr C2 and its word wx */
      L, UL, W, x, wx := ConstructSL2xSL2 (Cu);

      /* set up action of SL2 on each factor */
      _ := InitialiseGroup (L);
      assert #L`UserGenerators eq #W + 1;
      L`UserWords := [Rep(W)^0] cat W;

      sl2A := GoodCentraliser (Cu, L, 2, {3, 4});
      A := ExtractFactor (sl2A, [1, 2]);
      sl2B := GoodCentraliser (Cu, L, 2, {1, 2});
      B := ExtractFactor (sl2B, [3, 4]);

      /* multiply glue element by wreathing element 
         of SL wr C2 to obtain element of SL2 x SL2 */
      g := GlueElement (F);
      gx := g * x;
      // assert InBaseGroup (gx);

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
      wg := wa * wb * wx^-1;

      /* SL2 wr C2 to SL4 */
      T := Y`SLPGroup;
      gamma := hom < Cu`SLPGroup -> T | Cu`UserWords>;
      wg := gamma (wg);
   else 
      t3 := Cputime ();
      vprint User5: "Composition Tree call for degree", Degree (Y);
      T := CompositionTree (Y: KernelRank := 10, KnownLeaf := true);
      g := GlueElement (F);
      flag, wg := SolveWord (T, T[1], g);
assert flag;
assert T[1]`group`SLPGroupHom (wg) eq g;

      add := SLAdditionalElement (F);
      flag, wadd := SolveWord (T, T[1], add);
assert flag;
assert T[1]`group`SLPGroupHom (wadd) eq add;

      /* SL4 to C */
      wadd := ImagesOfWords (Y, C, [wadd]);
      wadd := wadd[1];

      /* C to G */
      T := G`SLPGroup;
      gamma := hom < C`SLPGroup -> T | C`UserWords cat [wu]>;
      wadd := gamma (wadd);
      add := Zero (MA);
      for i in [3..d - 2] do add[i][i] := 1; end for;
      add[1][2] := 1; add[2][d - 1] := 1; 
      add[d - 1][d] := 1; add[d][1] := -1;
      vprint User5: "Total Time in Composition Tree is ", Cputime (t3);
   end if; 

   /* SL4 to C */
   wg := ImagesOfWords (Y, C, [wg]);
   wg := wg[1];

   /* C to G */
   T := G`SLPGroup;
   gamma := hom < C`SLPGroup -> T | C`UserWords cat [wu]>;
   wg := gamma (wg);

   /* set up basis elements and words for G */

   basis := SLChosenElements (G: Words := false);

   A := basis[1];
   wa := W1[1]; 

   B1 := Identity (M);
   b1 := E1[2]; 
   MB := MatrixAlgebra (F, Nrows (b1));
   InsertBlock (~B1, MB!b1, 1, 1);
   B1 := GL(d, F)!B1; 
   wb1 := W1[2]; 

   Bg := Zero (M);
   Bg[1][d - 1] := 1; 
   Bg[2][d] := 1;
   Bg[d - 1][1] := 1;
   Bg[d][2] := 1;
   for i in [3..d - 2] do Bg[i][i] := 1; end for;
   Bg := GL(d, F)!Bg; 

   b2 := E2[2]; 
   B2 := Identity (M);
   MB := MatrixAlgebra (F, Nrows (b2));
   InsertBlock (~B2, MB!b2, f + 1, f + 1);
   B2 := GL(d, F)!B2; 
   wb2 := W2[2];

   /* produce d-cycle which maps 1 to 2 */
   if Degree (G) eq 4 then 
      B := Bg; 
      wb := wg;
   elif IsOdd (Degree (G)) and Degree (G2) eq 2 then
      B := B1 * B1^Bg; 
      wb := wb1 * wb1^wg; 
   elif IsOdd (Degree (G)) then  
      B := B1 * B1^Bg * B2^A;
      wb := wb1 * wb1^wg * wb2^wa; 
   elif IsEven (Degree (G)) and Degree (G2) eq 2 then
      B := B1 * Bg; 
      wb := wb1 * wg;
   elif IsEven (Degree (G)) then  
      B := B1 * Bg * B2; 
      wb := wb1 * wg * wb2; 
   end if;

   /* additional element to generate full symmetric group in even case */
   if FinalCall and IsEven (Degree (G)) then
      B := (add * B)^-1; 
      wb := (wadd * wb)^-1;
   end if;

   B := GL(d, F)!B; 

   T := basis[3];
   wt := W1[3]; 

   D := basis[4];
   wdelta := W1[4];

   gl := GL(d, F);
   E := [gl!A, gl!B, gl!T, gl!D];
   W := [wa, wb, wt, wdelta];
   vprint User5: "Time to get n-cycle and construct words is  ", Cputime (t3);
   return E, W;

end function;

/* recognize SL in its natural representation */

SLProcess := function (G, InputDimension: Scalars := false, Special := false)

   _ := InitialiseGroup (G: scalars := Scalars, generators := UserGenerators (G));
   d := Degree (G);
   F := BaseRing (G);

   if (Degree (G) lt 4) then 
      // "Call CompositionTree for degree ", d;
      X, Y := SLChosenElements (G);
      return X, Y, Identity (G);
   end if;

   /* if special, then split space of degree d = 4k + r as 4k and r */
   if Special and Degree (G) ne 5 then 
      r := d mod 4;
      if r eq 0 then 
         Range := [Degree (G) div 2]; 
         g, w, H, b, CB, dim := SpecialSplitSpace (G: IsCorrectType := MyIsLinearGroup);
      elif r eq 1 then 
         Range := [Degree (G) - 5]; 
         g, w, H, b, CB, dim := SplitSpace (G: Range := Range);
      else 
         Range := [Degree (G) - r]; 
         g, w, H, b, CB, dim := SplitSpace (G: Range := Range);
      end if;
   else 
      Range := [Degree(G) div 3..2 * Degree(G) div 3];
      if Degree (G) eq 5 then Range := [2, 3]; end if;
      g, w, H, b, CB, dim := SplitSpace (G: Range := Range);
   end if;

   H`SLPGroup := G`SLPGroup;
   H`UserGenerators := [CB * x * CB^-1: x in UserGenerators (G)];
   H`SLPGroupHom := MyHom (H, H`SLPGroup, UserGenerators (H));

   t1 := Cputime ();
   C := SpecialCentraliser (H, b, w, dim);
   C1 := GoodCentraliser (G, C, dim, {dim + 1..d});
   C2 := GoodCentraliser (G, C, d - dim, {1..dim});
   vprint User5: "Time to set up two SLs is ", Cputime (t1);
 
   G1 := ExtractFactor (C1, {1..dim});
   G2 := ExtractFactor (C2, {dim + 1..d});

   vprint User5: "Call 1 dimension of G1 is ", Degree (G1);
   E1, W1, CB1 := $$ (G1, InputDimension: Special := Special);
assert Verify (G1, E1, W1, CB1); 

   /* pull back words to G */
   W1 := [FactorToParent (G, C1, W1[i]): i in [1..#W1]];
   
   /* if special we can conjugate solution for G1 under element 
      of projective centraliser to obtain solution for G2 */

   if Special and (Degree (G) mod 4 eq 0) then 
      vprint User5: "Search for projective generator";
      theta, wtheta := ProjectiveGenerator (G, g, w);
      theta := CB * theta * CB^-1;
      /* now conjugate */
      W2 := [w^wtheta: w in W1]; 
      E2 := E1;
      LCB1 := CombineMatrices (CB1, CB1^0);
      B2 := [LCB1[i] : i in [1..dim]] cat [LCB1[i] * theta : i in [1..dim]];
      LCB2 := GL(d, F) ! &cat [Eltseq (b2): b2 in B2];
      CB2 := ExtractBlock (LCB2, dim + 1, dim + 1, dim, dim);
   else 
      vprint User5: "Call 2 dimension of G2 is ", Degree (G2);
      E2, W2, CB2 := $$ (G2, InputDimension: Special := Special);
assert Verify (G2, E2, W2, CB2); 
      W2 := [FactorToParent (G, C2, W2[i]): i in [1..#W2]];
   end if;

   Total := CombineMatrices (CB1, CB2);
   H := ApplyCOB (G, Total * CB);

   t1 := Cputime ();
   X, Y := SLGlue (H, G1, E1, W1, G2, E2, W2: FinalCall := Degree (H) 
                          eq InputDimension and IsEven (InputDimension));
   // assert Verify (G,X,Y,Total * CB);

   vprint User5: "Time to glue is ", Cputime (t1);
   return X, Y, Total * CB;
end function;

/* construct Steinberg generators of G */

SolveSL := function (G: Special := true)
   d := Degree (G);
   F := BaseRing (G);
   E, W, CB := SLProcess (G, d: Scalars := true, Special := Special);

   if d eq 2 or d eq 4 then return E, W, CB; end if;

   /* final base change to exhibit d-cycle correctly */
   cycle := E[2];
   wcycle := W[2];
   if IsEven (d) then 
      cycle := cycle^(d + 1);
      wcycle := wcycle^(d + 1);
   end if;
   H := sub <GL(d, F) | [CB * G.i * CB^-1: i in [1..Ngens (G)]]>;
   cb := SLNewBasis (H, cycle);
   E[2] := cb * cycle^-1 * cb^-1;
   W[2] := wcycle^-1;

   x := E[2];
   x := Sym (d)! [Depth (x[i]): i in [1..d]];
   assert #CycleStructure (x) eq 1;

   return E, W, cb * CB;
end function;
