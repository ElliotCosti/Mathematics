
ApplyCOB := function (G, CB)
   U := UserGenerators(G);
   U := [CB * U[i] * CB^-1: i in [1..#U]];
   d := Degree (G);
   F := BaseRing (G);
   K := sub <GL(d, F) | U>;
   K`UserGenerators := U;
   K`SLPGroup:=G`SLPGroup;
   K`UserWords:= G`UserWords;
   K`SLPGroupHom := MyHom (K, K`SLPGroup, U);
   return K;
end function;

exteriorsquare:= function(G)
/* G is natural copy of SL,set up G, find an involution and construct its centraliser */
Gens:=[];
gens:=[G.1,G.2];
for i in [3..10] do
gens[i]:=Random(G);
end for;


for i in [1..10] do
h:=gens[i];
Gens[i]:=ExteriorSquare(h);
end for;
d:=Degree(Gens[1]);
F:=BaseRing(G);
G:=sub<GL(d,F) | Gens>;
return G;

end function;

sections := function (G)
   M := GModule (G);
   F := BaseRing (G);
   d := Degree (G);
   CS, CF, COB := CompositionSeries (M);
   G`CompositionFactors := CF;
   G`ChangeOfBasis := GL(d, F)!COB;
   offset := 0;
   U := UserGenerators (G);
   E := [* *];
   for j in [1..#U] do 
      E[j] := MatrixBlocks (G, U[j]);
   end for; 
   section := [* *];
   for i in [1..#CF] do 
      k := Dimension (CF[i]);
      gens := [E[j][i]: j in [1..#U]];
      section[i] := sub < GL(k, F) | gens>;
      section[i]`UserGenerators := gens;
   end for;
   return section,COB;
end function;


embedmatrix := function (X, index, CB,cob)

   d := Degree (X);
   F := BaseRing (X);
   M := MatrixAlgebra (F, d);

   B := Identity (M);
   InsertBlock (~B, CB, index, index);
   B:=GL(d, F)!B;
  CB:=cob^-1*B*cob;
return CB;
end function;

/* two projective representations of G have same dimension;
   are they the same? try to find element of G 
   where char polys on each projection have different
   factorisations; if so we know they are distinct;
   if we can't find such an element, we believe
   they are the same */

AreRepresentationsIdentical := function (G, P1, P2: Limit := 10)
   if Degree (P1[3]) ne Degree (P2[3]) then return false; end if;
   repeat 
      Limit -:= 1;
      g := Random (G);
      a := ProjectionOfElement (G, P1, g);
      b := ProjectionOfElement (G, P2, g);
      ca := CharacteristicPolynomial (a);
      cb := CharacteristicPolynomial (b);
      fa := Factorisation (ca);
      fb := Factorisation (cb);
      if #fa ne #fb or {Degree (x[1]) : x in fa} ne {Degree(x[1]): x in fb} 
         then return false; end if;
  until Limit eq 0;
   return true;
end function;


/* G<=P, Factor is a quotient of G, we construct kernel of projection onto other factor, get Factor as a subgroup */

SLQuotientToSLSubgroup := function (P, G, Factor, n: Words := true)
  
   d := Degree (G);
   F := BaseRing (G);
   p := Characteristic (F);

   nmr := 0;
   A := [Identity (G)];
   if Words then 
      WA := [Identity (G`SLPGroup)];
   end if;
   flag, result := LieType (Factor[3], p);
   if flag then one := result[2] + 1; q := result[3]; else one := 0; q :=0; end if;
   
   repeat 
      if Words then 
         g, wg := RandomWord (G);
      else 
         g := Random (G);
      end if;
      b := ProjectionOfElement (G, Factor, g);
      o := Order (b);
      g := g^(o);
      nmr +:= 1;
      flag := false;  
      if IsIdentity (g) eq false then 
      Append (~A, g);
      if Words then 
         Append (~WA, wg^o);
      end if;
      H := sub <GL(d, F) | A>;
/* bug in recognising SL(4, 5) in certain reps */
      if Ngens (H) gt 1 then 
         flag, result := LieType (H, p);
         if flag then f := result[2] + 1; q := result[3]; else f := 0; q :=0; end if;
         flag := flag and f eq n - one and q eq #F;
      end if;
      if Ngens (H) gt 6 then flag := true; end if;
      end if;
   until  flag;

// vprint User5:
"Nmr checked to find non-trivial action = ", nmr;
"Ngens is ", Ngens (H);

   if Words then 
      theta := hom <G`SLPGroup -> P`SLPGroup | G`UserWords>;
      WA := [theta (w): w in WA];
   end if;

   H := sub < GL(d, F) | A >;
   if Words then 
      H`UserGenerators := A;
      H`UserWords := WA;
      H`SLPGroup := SLPGroup (#A);
      H`SLPGroupHom := MyHom (H, H`SLPGroup, H`UserGenerators);
   end if;

   return H, true;
end function;

/* G >= SL(e, F) x SL (d - e, f); try to locate each of  the SLs as a quotient */

ExploreCentraliser := function(G,n: Both := true) 
   d := Degree (G);
   F := BaseRing (G);
   p := Characteristic (F);
   H,cb := sections (G);
   for i in [1..#H] do 
      H[i]`SLPGroup := G`SLPGroup;
   end for;

   dims := [Degree (c): c in H];
   index := [i : i in [1..#dims]];
   Sort(~dims,~perm);
   index:=index^perm;

"dims are ", dims;

   /* identify the composition factors or their tensor factors */
   list := []; L := {};
   L := [* *]; N := [* *]; Dim := []; dim :=[]; P := []; NP := [];
      FacIndex := [];
   valid := {};
   for j in index do
      if Degree (H[j]) eq 1 then continue; end if;

      /* search for non-faithful action on factor */
      flag, result := LieType (H[j], p);
      if flag then f := result[2] + 1; q := result[3]; else f := 0; q :=0; end if;
      if flag and q ne #F then "Result flag,G1,index1:=SmallestFaithfulA(X,f);                /* G1 is SL(f) as section of X */ 
of LieType",  f, q; 
         error "1 bad involution"; 
      end if;
   
      if flag then 
         Append (~L, H[j]);
         Append (~Dim, f);
         Append (~dim, Degree (H[j]));
         Append (~P, j); 
         Append (~FacIndex, 0); 
         continue; 
      end if;
 
      /* tensor factors */
      flag := IsTensor (H[j]);
      "RESULT of tensor is ", flag;
      if flag cmpeq true then 
      T := TensorFactors (H[j]);
      for i in [1..2] do 
         flag, result := LieType (T[i], p);
         if flag then f := result[2] + 1; q := result[3]; else f := 0; q :=0; end if;
         if flag and q ne #F then "f, q are ", f, q; 
            error "2 bad involution";  end if;
         if not flag then
            flag :=  IsLinearGroup (T[i]) ;
            if not flag then continue; end if;
            f := Degree (T[i]);
         end if;
         Append (~FacIndex, i); 
         Append (~L, T[i]);
         /* factor is isomorphic to SL(f) */
         Append (~Dim, f);
         /* presents in this dimension */
         Append (~dim, Degree (T[i]));
         Append (~P, j);
      end for;
      end if;
   end for;

   facdims := Set (Dim);

   /* special cases - n = 4 or 5 */
   if n eq 4 and 4 in facdims then Include (~facdims, 0); end if;
   if n eq 5 and 4 in facdims then Include (~facdims, 1); end if;

"factor dimensions found are ", facdims;

   if exists(z){[x, y]: x in facdims, y in facdims | x + y eq n} then 
     f := Maximum (z);
     rem := n - f;
   else 
      error "3 bad involution";  
   end if;

   // assert #facdims le 2;
   if Both and f in {n - 1, n} then error " f in {n-1,n), bad involution";  end if;

   /* smallest dim repn for each factor */

   /* first representation */
   I := [i : i in [1..#dim] | Dim[i] eq f];
   X := [dim[i]: i in I];
   min, pos := Minimum (X);
   index := I[pos];
"P is ", P;
   Fac1 := <H[P[index]], P[index], L[index], FacIndex[index]>;

   /* special case - n = 5 */
   if rem eq 0 then return true, Fac1, Fac1, f, 0; end if;
   if rem eq 1 then return true, Fac1, Fac1, f, 1; end if;

   /* second representation */
   exclude := [index];
"TRY TO GET SECOND";
   repeat 
      I := [i : i in [1..#dim] | Dim[i] eq rem and not (i in exclude)];
      X := [dim[i]: i in I];
      min, pos := Minimum (X);
      index2 := I[pos];
      Fac2 := <H[P[index2]], P[index2], L[index2], FacIndex[index2]>;
   until not AreRepresentationsIdentical (G, Fac1, Fac2);

   return true, Fac1, Fac2, f, rem;
end function;


/* choose smallest section of X having faithful action */

SmallestFaithfulA := function (X, f)
   S,cob := sections (X); 
   F := BaseRing (X);
   p := Characteristic (F);
   d:=Degree(X);
   cob:=GL(d,F)!cob;
   Deg := [Degree (s): s in S];Deg;

   index := [i : i in [1..#Deg]];
   Sort (~Deg, ~perm);
   index:=index^perm;
   for i in index do
      if Degree (S[i]) eq 1 then continue; end if;
      flag, result :=LieType (S[i], p);
      if flag then k := result[2] + 1; q := result[3]; else k := 0; q :=0; end if;
      if flag and k eq f and q eq #F then 
         return true, S[i], i,cob; end if;
   end for;
   return false, _, _,_;
end function;






constructcentraliser := function(G,n)
/* find an involution g in G with word w on X, and construct its centraliser */


repeat
      g, w, H, b, CB, dim := SplitSpace (G :  SortSpaces := false);
      "dim is ", dim;
      H`SLPGroup := G`SLPGroup;
      H`UserGenerators := [CB * x * CB^-1: x in UserGenerators (G)];
      H`SLPGroupHom := MyHom (H, H`SLPGroup, UserGenerators (H));
      C := CentraliserOfInvolution (H, b, w);
      C := MyDerivedCentraliser (G, C);
      "IsIrred? ", IsIrreducible (C);
until IsIrreducible (C) eq false;

return g,w,H,b,CB,dim,C;

end function;




GetSL2s := function (G, n, CB, CG1, CG2, G1, E1, W1, G2, E2, W2)
   wb1 := W1[2];

   
   
   /* construct u = Diagonal ([1, ... 1, -1, -1]) */
   delta := E1[4]; o := Order (delta); 
   u:=delta^(o div 2); u:=u^((E1[2])^-2);
   wdelta := W1[4]; wu := wdelta^(o div 2); wu := wu^(wb1^-2);
   S1 := Parent (wu);
   
   S := G`SLPGroup; SC1 := CG1`SLPGroup; SC2 := CG2`SLPGroup; 

   /* write wu as word in user-generators of G */
   h := hom <S1 -> SC1 | [SC1.i: i in [1..Ngens (S1)]]>;
   gamma := hom <SC1 -> S | CG1`UserWords>;
   h := h * gamma;

   wu := h (wu);
                   

   /* construct v = Diagonal ([-1, -1, 1, ... 1]) */
   delta := E2[4]; o := Order (delta); 
   v:=delta^(o div 2);
   wdelta := W2[4]; wv := wdelta^(o div 2);
   S2 := Parent (wv);

   h2 := hom <S2 -> SC2 | [SC2.i: i in [1..Ngens (S2)]]>;
   gamma := hom <SC2 -> S | CG2`UserWords>;
   h2 := h2 * gamma;

   wv := h2 (wv);

   /* w is word for 
      uv = Diagonal ([ 1, ..., 1, -1, -1, -1, -1, 1, ... 1])
      where -1s are in position f - 1, ... f + 2 */
   wI := wu * wv;

 H := ApplyCOB (G, CB);

  
   
   u:=H`SLPGroupHom(wu);
   /*assert Order(u) eq 2;*/
   
   v:=H`SLPGroupHom(wv);
   /*assert Order(v) eq 2;*/
   

   /* set up matrix I for uv */
   I := H`SLPGroupHom (wI);
   
   //assert Dimension(Eigenspace(I,-1)) eq 4;

   /* generate two SL2s in SL4 */
   WBase :=[h(W1[1]^W1[2]^-2), h(W1[3]^W1[2]^-2), h(W1[4]^W1[2]^-2)];
   Base := [H`SLPGroupHom (w): w in WBase];
   WBase2 := [h2 (W2[1]), h2(W2[3]), h2(W2[4])];
   Base2 := [H`SLPGroupHom (w): w in WBase2];

return u,wu,v,wv,I,wI,Base,WBase,Base2,WBase2,h,h2,H;

end function;

SL4Pt1 := function (G, H, I, wI, wu, n, Base, Base2, WBase, WBase2)

   d := Degree (G);
   F := BaseRing (G);

   /* construct GL(4) x GL(d - 4) as centraliser of I */
   if n eq 4 then 
      largeC := H; 
   else 
      largeC := CentraliserOfInvolution (H, I, wI);
   end if;

   CI:=MyDerivedCentraliser(H,largeC);  
   flag, P1, P2, f, rem := ExploreCentraliser (CI, n: Both := false);

   if f eq rem then 
      CI := MyDerivedCentraliser (H, CI);
      flag, P1, P2, f, rem := ExploreCentraliser (CI, n: Both := false);
   end if;

   /* construct C = SL(4) as subgroup of G */

   /* if both factors have same dimension, must decide which
      is section to construct subgroup */
   if f eq 4 and f eq rem then 
      /* if SL(4) section commutes with elements of Base, then 
        use action on this section to obtain other SL4 as subgroup;
        we want to construct the SL4 subgroup which  does not 
        commute with the SL2 */

      A := [ProjectionOfElement (CI, P2, Base[i]): i in [1..#Base]];
      if SectionsCommute (P2[3], A) then 
         C := SLQuotientToSLSubgroup (H, CI, P2, n);
      else 
         A := [ProjectionOfElement (CI, P1, Base[i]): i in [1..#Base]];
         assert SectionsCommute (P1[3], A); 
         C := SLQuotientToSLSubgroup (H, CI, P1, n);
      end if;
   elif f eq 4 and rem in {0, 1} then 
      "4 or 5-dimensional case";
      C := CI;
   elif f eq 4 then
   C := SLQuotientToSLSubgroup (H, CI, P2, n);
   else
      assert rem eq 4;
      C := SLQuotientToSLSubgroup (H, CI, P1, n);
   end if;

   /* potential scalars arising from tensor products */
   C := MyDerivedCentraliser (H, C);
 
   /* modify C to include u as generator */
   large := H`SLPGroupHom (wu);
   C := RedefineGroup (H, C, large, wu);
   mm := #C`UserGenerators;
   m := Ngens (C);

   flag, G1, index := SmallestFaithfulA (C, 4);
   S := <G1, index, G1, 0>;
   /* construct GL(2) wr C2 as subgroup of C;
      more correctly this is SL(2, q) x SL(2, q) with 
      D_2n = <q - 1, 2> acting on the SL2s  */

   Cu := ProjectiveCentraliserOfInvolution (C, S, C.m, C`SLPGroup.mm: N := 10);

return Cu,C;

end function;


SL4Pt2:= function(G,Cu,C,Base,WBase,Base2,WBase2)

  d := Degree (G);
   F := BaseRing (G);


   /* two copies of SL2 in Cu */
   X := sub<GL(d, F) | Base>; 
   _ := InitialiseGroup (X: scalars := false);
   // RandomSchreier (X);
   X`UserWords := WBase;
   Y := sub<GL(d, F) | Base2>; 
   _ := InitialiseGroup (Y: scalars := false);
   Y`UserWords := WBase2;
   // RandomSchreier (X);
   // "Orders of 2 SLs is ", #X, #Y;
   // assert #X eq #Y; 
   
   /* find wreathing element to map X to Y and then
      element Yb of Y which maps base for X^wr to base for Y ;
      similarly find element Xb which maps base for Y^wr to base for X */
count1:=0;
   repeat
      count2:=0; 
      repeat
         count2:=count2+1;
         wr, word := RandomWord (Cu);
         Z := X^wr;
         Z`UserGenerators := [x^wr : x in UserGenerators (X)];
         flag := ElementsActReducibly (Y, UserGenerators (Z));
         if flag then 
            Z := Y^wr;
            Z`UserGenerators := [x^wr : x in UserGenerators (Y)];
            flag := ElementsActReducibly (X, UserGenerators (Z));
         end if;
         "Wreating element found? ", flag;
                                                    
      until (flag eq true) or (count2 eq 50);

      assert X^wr subset Y and Y^wr subset X;

      flag, Y1, index,cob := SmallestFaithfulA (Y, 2);
      Z := X^wr;
      Z := [MatrixBlocks (Y, Z.i)[index]: i in [1..Ngens (Z)]];
      Yb := ConjugateSL2Bases (Y1, Z, [Y1.i : i in [1..Ngens (Y1)]]);

      flag, X1, index := SmallestFaithfulA (X, 2);
      Z := Y^wr;
      Z := [MatrixBlocks (X, Z.i)[index]: i in [1..Ngens (X)]];
      Xb := ConjugateSL2Bases (X1, Z, [X1.i : i in [1..Ngens (X1)]]);
count1:=count1+1;
   until( Determinant (Xb) eq 1 and Determinant (Yb) eq 1) or (count1 eq 50);

   flag := RecognizeSL2 (X1);
   flag, wx := MySL2ElementToWord (X1, Xb);
   flag := RecognizeSL2 (Y1);
   flag, wy := MySL2ElementToWord (Y1, Yb);

   /* words for conjugating elements back to X1, Y1 */
   wx := ImagesOfWords (X1, X, [wx])[1];
   wy := ImagesOfWords (Y1, Y, [wy])[1];
   
   /* back to G */
   theta := hom <X`SLPGroup -> G`SLPGroup | X`UserWords>;
   wx := theta (wx);
   theta := hom <Y`SLPGroup -> G`SLPGroup | Y`UserWords>;
   wy := theta (wy);

   /* pull wr back to G */
   theta := hom <Cu`SLPGroup -> C`SLPGroup | Cu`UserWords>;
   word := theta (word);
   theta := hom <C`SLPGroup -> G`SLPGroup | C`UserWords>;
   word := theta (word);

   /* glue element */
   glue := word * wx * wy;
   return true, glue; 

end function;
getelementsandwords:= function(G,H,n,Base,WBase,Base2,WBase2,h,h2,W1,W2,glue);

wg:=glue;
  /* set up basis elements and words for G */
   wa := W1[1]; 
   wa := h(wa);
Order (G`SLPGroupHom (wa));

   wb1 := W1[2]; 
   wb1 := h(wb1);

   wb2 := W2[2];
   wb2 := h2(wb2);

   wb := wb1 * wg * wb2; 
"order of b1 ", Order (G`SLPGroupHom (wb1));
"order of g ", Order (G`SLPGroupHom (wg));
"order of b2 ", Order (G`SLPGroupHom (wb2));
"order of b ", Order (G`SLPGroupHom (wb));
"P order of b ", ProjectiveOrder (G`SLPGroupHom (wb));

   wt := W1[3]; 
   wt := h(wt);

   wdelta := W1[4];
   wdelta := h(wdelta);

   /* we have 3 permutations
      B1 := (1, f, -(f-1), .., -2);
      Bg := (f - 1, f + 1)(f, f+ 2);
      B2 = (f + 1, d, -(d - 1), ..., -(f + 2);
      and we can produce transpositions
      (a, b) where a, b in {1..f} or a, b in {f + 1..d}; 
      use these to produce an n-cycle of the form (1, 2, ...) */

   if n ge 6 then 
      first := wa^(wa^wb1^-1);
      second := wa^(wa^(wa^(wb1^-1) * wa^(wb1^-2)));
      third := h(W1[1]);
      wb := first * second * third * wb;
   elif n eq 5 then 
      wb := wb2 * wg * wa^3;

   elif n eq 4 then
      Bg := G`SLPGroupHom (wg);
Order (Bg);
assert Order (Bg) eq 2;
      B1 := G`SLPGroupHom (wb1);
Order (B1);
assert Order (B1) eq 2;
      x := Bg^B1; wx := wg^wb1; 
assert Order(x) eq 2;
      C := CentraliserOfInvolution (G, x, wx);
"#C is ", #C;
      y := (B1 * Bg)^2; wy := (wb1 * wg)^2;
assert Order (y) eq 2;
assert Bg in C;
assert y in C;
assert exists{s : s in C | Bg^s eq y};
      flag, s, ws := ConjugateInvolutionsWords (C, Bg, wg, y, wy);
      while Order (s) gt 2 do 
         s := y * s;
         ws := wy * ws;
      end while;
      wb := wb1 * ws * wg * wb1;
      assert Order (wb) eq n;

   else 
      error "should not be here";
   end if;

   W := [wa, wb, wt, wdelta];
   E := [G`SLPGroupHom (w): w in W];
   return E, W;

end function;






SLGrey2 := function(G,n: Scalars:=true);



F:=BaseRing(G);
q:=Characteristic(F);





if Degree (G) eq n and n le 4 then return SLProcess (G, n: Scalars := Scalars); end if; 


_:=InitialiseGroup(G: scalars := Scalars, generators := UserGenerators (G));


"SplittingProcess";
"finding involution, constructing centraliser";
g,w,H,b,CB,dim,C := constructcentraliser(G,n); /*find involution, construct centraliser */


flag,P1,P2,f,rem := ExploreCentraliser(C,n);   /* find SL(f) and SL(rem) as sections of C */

if (Degree(P1[1]) eq 4)  then
flag,result:= LieType(P1[1],q);
if flag eq false then error " not SL4";
end if; end if;

if (Degree(P2[1]) eq 4)  then
flag,result:= LieType(P2[1],q);
if flag eq false then error " not SL4";
end if; end if;



X:=SLQuotientToSLSubgroup(G,C,P2,n);
X := MyDerivedCentraliser (G, X);
flag,G1,index1,cob1:=SmallestFaithfulA(X,f);     /* G1 is SL(f) as section of X */ 
if not flag then error "bad centraliser"; end if;

Y,flag := SLQuotientToSLSubgroup(G,C,P1,n);    /* SL(rem) isomorphic to Y <= C */
Y := MyDerivedCentraliser (G, Y);
flag, G2, index2,cob2 := SmallestFaithfulA (Y, rem);
 if not flag then error "bad centraliser"; end if;


"recursion";
E1,W1,CB1:= $$(G1,f: Scalars:=false);
"embedding CB1";
CB1 := embedmatrix (X, index1, CB1,cob1);
"embedded CB1";
W1:=ImagesOfWords(G1,X,W1); 

"recursion";
E2,W2,CB2 := $$(G2,rem: Scalars:=false);
"embedding CB2";
CB2 := embedmatrix (Y, index2, CB2,cob2);
"embedded CB2";
W2:=ImagesOfWords(G2,Y,W2); 

//elements1:= ImagesOfElements(X,W1,CB1);
//elements2:= ImagesOfElements(Y,W2,CB2);
Total := CB1 * CB2*CB;

"constructing SL2s";
u,wu,v,wv,I,wI,Base,WBase,Base2,WBase2,h,h2,H:=GetSL2s(G,n,Total,X,Y,G1,E1,W1,G2,E2,W2); 

"constructing Cu and C";
Cu,C:=SL4Pt1 (G, H, I, wI, wu, n, Base, Base2, WBase, WBase2);

"getting glue element";
flag,glue:= SL4Pt2(G,Cu,C,Base,WBase,Base2,WBase2);

E,W:=getelementsandwords(G,H,n,Base,WBase,Base2,WBase2,h,h2,W1,W2,glue); 



return E,W,Total;


end function;
