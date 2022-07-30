forward SolveSmaller;

ImageSpace := function (G)
   d := Degree (G);
   F := BaseRing (G);
   V := VectorSpace (F, d);
   MA := MatrixAlgebra (F, d);
   list := [];
   for i in [1..Ngens (G)] do 
      g := G.i;
      g := MA!g;
      gm1 := g - Id(MA);
      list cat:= [gm1[i] : i in [1..d]];
   end for;
   I := sub<V | list>;
   return I;
end function;

KernelSpace := function (G)
   d := Degree (G);
   F := BaseRing (G);
   V := VectorSpace (F, d);
   MA := MatrixAlgebra (F, d);
   list := [];
   N := V;
   for i in [1..Ngens (G)] do 
      g := G.i;
      g := MA!g;
      gm1 := g - Id(MA);
      N meet:= Nullspace (gm1);
   end for;
   return N;
end function;

/* find element of H mapping v to u and element of K mapping w to u,
   and so an element of G mapping v to w */

FindVector := function (IH, IK, H, K, v, w)

   t := v - w;
   /* a in IH, b in IK */
   a, b := DecomposeVector (IH, t);
   assert a in IH;
   assert b in IK;

   assert w + b - v in IH;

   u := w + b;
   
   ker := KernelSpace (H);
   if v in ker then return false; end if;
   /* v0 in ker, v1 in IH */
   v0, v1 := DecomposeVector (ker, v);
/* 
   if v0 eq Zero (V) or v1 eq Zero (V) then
   "1";   return false;
   end if;
*/

   u1 := u - v0;
   /* needs to be done correctly */
   // flag := exists(h){h : h in H | v1^h eq u1};
   // assert flag;
   HH := {h : h in H | v1^h eq v1};
   h := Random (HH);
   assert v1^h eq u1;
   assert v^h eq u;

   ker := KernelSpace (K);
   if w in ker then return false; end if;

   /* w0 in ker, w1 in IK */
   w0, w1 := DecomposeVector (ker, w);
/* 
   if v0 eq Zero (V) or v1 eq Zero (V) then
   "2";   return false;
   end if;
*/

   u1 := u - w0;
   /* needs to be done correctly */
   KK := {k : k in K | w1^k eq u1};
   // flag := exists(k){k : k in K | w1^k eq u1};
   // assert flag;
   k := Random (KK);
   assert w1^k eq u1;
   assert w^k eq u;

   return h * k^-1;
end function;

/* given v, w vectors produce g in G such that v^g = w */
VectorSolution := function (G, H, K, v, w)
   
   d := Degree (G);
   F := BaseRing (G);
   V := VectorSpace (F, d);
   IH := ImageSpace (H);
   IK := ImageSpace (K);
   if IH + IK ne V then return false; end if;

   return FindVector (IH, IK, H, K, v, w);

end function;

/* construct Steinberg basis for G = SL (3, q);
   do this by first solving an SL2, then another SL2 */

SolveSL3 := function (G)
   InitialiseGroup (G);
   F := BaseRing (G);
   d := Degree (G);
   ranks := [2];

   /* construct SL2 as subgroup */
   H, rank, COB := ConstructSmallerSL (G, ranks);
   K := ExtractGroup (H, [1..2]);
   A, WA, CA := SolveSmaller (K);
   WA  := ImagesOfWords(K, H, WA);
   WA := [PullbackWord (G, H, w): w in WA];

   /* construct conjugate of H and solve this conjugate */
   g, w := RandomWord (G);
   K := ApplyCOB (H, g^-1);
   B := A;
   WB := [wa^w: wa in WA];
   // CB := CA^g;

   /* construct random elements of SL(3, q) which fix V.1
      and obtain 1     0    
                 * SL(2, q)    */

   V := VectorSpace (F, d);
   v := V.1;
   X := [GL(d, F) | ];
   repeat 
      r := VectorSolution (G, H, K, v, v);
      Append (~X, r);
      S := sub <GL(d, F) | X>;
      s := Sections (S);
   until #s eq 2;
    
/* 
   repeat x, wx := Random (G); until v^x eq v;
   repeat y, wx := Random (G); until v^y eq v;
   repeat z, wx := Random (G); until v^z eq v;
   X := sub<G | x, y, z>;
   InitialiseGroup (X);
   s := Sections (X);
   s;
*/

   /* now clean up D to obtain SL3 as subgroup of G */
   gens, W := Degree3LinearProblem (G, D, 1);
   gens := [x^2: x in gens];
   W := [w^2: w in W];

end function;
