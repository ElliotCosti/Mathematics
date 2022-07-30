forward ElementActsFPF, PullbackWord, ApplyCOB;

OddOrderGenerators := function (G, C, action: Words := true)

   d := Degree (C); F := BaseRing (C);
   gens := []; words := [];
   found := false;
   repeat
      if Words then 
         x, wx := RandomWord (C);
      else
         x := Random (C);
      end if;
      y := ExtractAction (x, action);
      if IsOdd (Order (y)) then
         Append (~gens, x);
         if Words then Append (~words, wx); end if;
         O := sub <GL(d, F) | gens>;
         S := Sections (O);
         flag := exists(i){i : i in [1..#S] | Degree (S[i]) eq #action};
         if flag then S := S[i]; found := MyIsLinearGroup (S); end if;
      end if;
   until found;
   D := sub <GL(d, F) | gens>;
   _ := InitialiseGroup (D : generators := gens);
   W := [wx^0] cat words;
   D`UserWords := [PullbackWord (G, C, w): w in W];

   return D;
end function;

/* z is generator of SL, x is our chosen element of order k */
Formula := function (x, z)
   k := Order (x);
   return x * z * (x * x^z)^((k - 1) div 2);
end function;

/* z is generator of SL, x is our chosen element of order k */
FormulaWord := function (x, z, k)
   return x * z * (x * x^z)^((k - 1) div 2);
end function;

/* find element which can be used to apply the Formula */

FormulaElement := function (G, H, m: Words := true)

   F := BaseRing (H);
   q := #F;
   d := Degree (H);

   H := KillFactor (G, H, [[m + 1..d - m]], [[1..m], [d - m + 1..d]]: 
                       Words:=true);

   index := m + 1;
   h, w := ElementActsFPF (H, index, d - 2 * m);
   w := PullbackWord (G, H, w);
   E := Eigenspace (h, 1);

//   "Investigated ", nmr, "elements to find suitable formula element";

   /* use eigenvectors from eigenspace to change basis */
   d := Degree (H);
   MA := MatrixAlgebra (F, d);
   V := VectorSpace (GF (q), d);
   CB := &cat[Eltseq (E.i): i in [1..m]] cat &cat[Eltseq (V.i) : i in [m + 1..d]];
   CB := MA ! CB;
   h := CB * h * CB^-1;

   MB := KMatrixSpace (F, d - 2 * m, d);

   hm1 := h - Identity (MA);
   X := MB ! &cat[Eltseq (V.i) : i in [m + 1..d - m]];
   Y := X * hm1;
                                                                                
   /* use eigenvectors from eigenspace to change basis */
   CB1 := Identity (MA);
   InsertBlock (~CB1, Y, m + 1, 1);
                                                                                
   /* h should have m x m identity block, 2m x 2m block,
      m x m identity block, everything else zero */
   h := GL(d, F) ! (CB1 * h * CB1^-1);

   return h, w, CB1 * CB;

end function;

/* find an element of odd order of G whose restriction to 
   SL(m, q) does not have eigenvalue 1 */

ElementActsFPF := function (G, index, m)
   nmr := 0;
   repeat
      g, w := RandomWord (G);
      s := ExtractBlock (g, index, index, m, m);
      o := Order (s);
      EV := Eigenvalues (s);
      ev := {x[1]: x in EV};
      nmr +:= 1;
      if nmr mod 100 eq 0 then "FPF trial ... ", nmr; end if;
   until IsOdd (o) and not (1 in ev);

   vprint Involution: "Tested ", nmr, "elements to find FPP";

   return g^2, w^2;
end function;

/* apply Formula to clean up matrix g in G having general shape
       A  *  *
       0  B  * 
       0  0  C
   where A and C are independent rank m matrices,
   B is rank d - 2m matrix;

   hence produce SL(m), SL(d - 2m), SL(m) as subgroups of G;
   P is parent of G, rewrite words corresponding to SL 
   generators as words in P */
  
FormulaABC := function (P, G, m: Words := true)

   F := BaseRing (G);
   d := Degree (G);
   MA := MatrixAlgebra (F, d);

   /* formula element */
   h, wh, COB := FormulaElement (P, G, m);

   Q := ApplyCOB (G, COB);

   /* fix up top SL */
   C := KillFactor (P, Q, [[1..m]], [[m + 1..d - m], [d - m + 1..d]]: 
                       Words:=true);
   C := OddOrderGenerators (P, C, [1..m]);

   /* clean up this SL(m, q) using formula */
   U := UserGenerators (C);
   gensC := [Formula (h, U[i]): i in [1..#U]];
   CC := sub <GL (d, F) | gensC>;
   _ := InitialiseGroup (CC : generators := gensC, scalars := false);
   W := C`UserWords;
   CC`UserWords := [FormulaWord (wh, W[i], Order (h)): i in [1..#W]];
  
   D := KillFactor (P, Q, [[d - m + 1..d]], [[m + 1..d - m], [1..m]]: Words:=true);
   D := OddOrderGenerators (P, D, [d - m + 1..d]);

   /* clean up this SL(m, q) using formula */
   U := UserGenerators (D);
   gensD := [Formula (h, U[i]): i in [1..#U]];
   DD := sub <GL (d, F) | gensD>;
   _ := InitialiseGroup (DD : generators := gensD, scalars := false);
   W := D`UserWords;
   DD`UserWords := [FormulaWord (wh, W[i], Order (h)): i in [1..#W]];

   lg, wlg := ElementActsFPF (DD, d - m + 1, m);
   wlg := PullbackWord (P, DD, wlg);

   E := Eigenspace (lg, 1);
   assert Dimension (E) eq d - m;
   /* use eigenvectors from eigenspace to change basis */
   V := VectorSpace (F, d);
   CB4 := &cat[Eltseq (E.i): i in [1..m]] cat 
         &cat[Eltseq (V.i) : i in [m + 1..d]];
   CB4 := MA ! CB4;

   /* formula element to clean up top-left */
   lg := GL(d, F)! (CB4 * lg * CB4^-1);

   CC2 := ApplyCOB (CC, CB4);
   /* produce one SL(m, q) */
   U := UserGenerators (CC2);
   gensL := [Formula (lg, U[i]): i in [1..#U]];
   L := sub <GL (d, F ) | gensL>;
   _ := InitialiseGroup (L : generators := gensL, scalars := false);
   W := CC2`UserWords;
   L`UserWords := [FormulaWord (wlg, W[i], Order (lg)): i in [1..#W]];

   /* formula element to clean up bottom right */
   rg, wrg := ElementActsFPF (L, 1, m);
   wrg := PullbackWord (P, L, wrg);
   E := Eigenspace (rg, 1);
   assert Dimension (E) eq d - m;

   /* second SL(m, q) */
   U := UserGenerators (DD);
   gensR := [Formula (rg, U[i]): i in [1..#U]];
   R := sub < GL (d, F) | gensR>;
   _ := InitialiseGroup (R : generators := gensR, scalars := false);
   W := DD`UserWords;
   R`UserWords := [FormulaWord (wrg, W[i], Order (rg)): i in [1..#W]];

   /* 3rd SL of dimension d - 2m */
   B := KillFactor (P, Q, [[m + 1..d - m]], [[d - m + 1..d], [1..m]]: 
                      Words:=true);
   U := UserGenerators (B); 
   X := [Formula (lg, U[i]): i in [1..#U]];
   Y := [Formula (rg, X[i]): i in [1..#X]];
   S := sub < GL(d, F) | Y>;
   _ := InitialiseGroup (S : generators := Y, scalars := false);

   W := B`UserWords;
   X := [FormulaWord (wlg, W[i], Order (lg)): i in [1..#U]];
   Y := [FormulaWord (wrg, X[i], Order (rg)): i in [1..#X]];
   S`UserWords := Y;

   return L, R, S, COB * CB4;
end function;

/* apply Formula to centraliser of form A * * ; 0 B * ; 0 0 A
   to obtain A 0 * ; 0 I 0; 0 0 A and I 0 0 ; 0 B 0 ; 0 0 I */
 
FormulaAB := function (G, C, m, h, wh, COB)
 
   d := Degree (C);
   F := BaseRing (C);

   Q := ApplyCOB (C, COB);

   A := KillFactor (G, Q, [[1..m],[d - m + 1..d]], [[m + 1 .. d - m]]: 
                        Words := true);

   /* clean up this SL(m, q) using formula */
   U := UserGenerators (A);
   gensA := [Formula (h, U[i]): i in [1..#U]];
   W := A`UserWords;
   W := [FormulaWord (wh, W[i], Order (h)): i in [1..#W]];

   A := sub <GL (d, F) | gensA>;
   _ := InitialiseGroup (A : generators := gensA, scalars := false);
   A`UserWords := W;

   rg, wrg := ElementActsFPF (A, 1, m);
   wrg := PullbackWord (G, A, wrg);

   B := KillFactor (G, Q, [[m + 1..d - m]], [[1..m], [d - m + 1..d]]: 
                     Squares := true, Words:=true);

   /* clean up this SL(d - 2 * m, q) using formula */
   U := UserGenerators (B);
   gensB := [Formula (rg, U[i])^2: i in [1..#U]];
   W := B`UserWords;
   W := [FormulaWord (wrg, W[i], Order (rg))^2: i in [1..#W]];
   B := sub <GL (d, F) | gensB>;
   _ := InitialiseGroup (B : generators := gensB, scalars := false);
   B`UserWords := W;

   return A, B;
end function;
