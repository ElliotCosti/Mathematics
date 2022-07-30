NontrivialElt := function (G, H, A2, index, g, wg)
   B := SL2Basis (A2);
   wbasis := B[2];
   wy := B[2][index][1]^2;
   wy := PullbackWord (H, A2, wy);
   y := H`SLPGroupHom (wy);
   wy := PullbackWord (G, H, wy);
   if Order (g * y) gt 2 then 
      return true, g * y, wg * wy;
   else 
      return false, _, _;
   end if;
end function;

/* 
   0 1  X    *  1  0  X             0  1   0
   1 0          0  1          =     1  0   
    0   I        0    I               0    I 
             
     R       *    S           =        T

   We can construct R and want to construct T as word;
   to do this we construct S and take product R * S to obtain T
*/

LinearProblem := function (G, H)

   K := BaseRing (G);
   repeat 
      A, _, WA := KillFactor (G, H, [[1,2]], [[3,4]] : Words:=true, Parent := true);
      A2 := ExtractGroup (A, [1,2]);
      A2`UserWords := WA;
      flag := RecognizeSL2 (A2, #BaseRing (A2) : Verify := false);

      x := GL(2, K) ! [0, 1, 1, 0];
      flag, w := MySL2ElementToWord (A2, x);
      w := PullbackWord (H, A2, w);
      y := H`SLPGroupHom (w);
      w := PullbackWord (G, H, w);

      /* construct element S of form I  * by squaring R = y 
                                     0  I                     */

      hold := y;
      whold := w;
          
      if Order (y) eq 2 then 
         flag, y, w := NontrivialElt (G, H, A2, 1, hold, whold);
         if not flag then 
            flag, y, w := NontrivialElt (G, H, A2, 3, hold, whold);
         end if;
         if flag then 
            hold := y;
            whold := w;
         else 
            "Both squares evaluated to trivial -- try again";
         end if;
      end if;
   until Order (hold) eq 4;

   if Order (y) eq 4 then 
      y := y^2; w := w^2;
   end if;

   assert Order (y) eq 2;

   Y := ExtractBlock (y, 1, 3, 2, 2);
   if Rank (Y) eq 0 then return y, w; end if;

   B, _, WB := KillFactor (G, H, [[3,4]], [[1,2]] : Words:=true, Parent := true);

   /* construct element of corank 2 */
   while Rank (Y) ne 2 do 
      a, wa := RandomWord (A);
      wa := PullbackWord (G, A, wa);
      b, wb := RandomWord (B);
      wb := PullbackWord (G, B, wb);
      flag, y, w := Variations (y^a, w^wa, y^b, w^wb, 2);
      Y := ExtractBlock (y, 1, 3, 2, 2);
   end while;

   assert Rank (Y) eq 2;
     
   // K := CoefficientRing(G);
   k := Degree (K);
   p := Characteristic (K);
   F := GF(p);

   V := VectorSpace (F, 4 * k);

   /* obtain basis for V */
   I := []; wI := []; basis := [];
   repeat
      a, wa := RandomWord (A);
      wa := PullbackWord (G, A, wa);
      v := y^a;
      S := sub < V | basis>;
      u := V! &cat[Eltseq (x): 
              x in &cat[Eltseq (ExtractBlock (v, 1, 3, 2, 2))]];
      if not u in S then Append (~I, a); Append (~wI, wa);
         Append (~basis, u); end if;
   until S eq V;

   /* express u as linear combination of basis */
   u := V!&cat[Eltseq (x): x in &cat[Eltseq (ExtractBlock (hold, 1, 3, 2, 2))]];
   M := MatrixAlgebra (F, 4 * k) ! &cat[Eltseq (x): x in basis];
   flag, coords := IsConsistent (M, u);
   assert coords * M eq u;

   coords := [Integers ()! x : x in Eltseq (coords)];
   product := &*[(y^I[i])^coords[i]: i in [1..#coords]];
   word := &*[(w^wI[i])^coords[i]: i in [1..#coords]];

   /* this is glue element */
   g := GL (4, K) ! [0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1];
   assert product * hold eq g;
   return g, word * whold;

end function;

ObtainBasis := function (G, A, B, y, V, m: Limit := 3 * Degree (V))

   d := Degree (G); K := BaseRing (G);
   p := Characteristic (K);
   F := GF(p);

   /* obtain basis for V */
   I := [GL(d, K) | ]; wI := []; basis := [];
   nmr := 0;
   repeat
      a, wa := RandomWord (A);
      wa := PullbackWord (G, A, wa);
      v := y^a;
      nmr +:= 1;
      S := sub < V | basis>;
      u := V! ((&cat[Eltseq (x): 
              x in &cat[Eltseq (ExtractBlock (v, 1, m + 1, m, d - 2 * m))]])
            cat 
      (&cat[Eltseq (x): 
         x in &cat[Eltseq (ExtractBlock (v, m + 1, d - m + 1, d - 2 * m, m))]]));
      if not u in S then Append (~I, a); Append (~wI, wa);
         Append (~basis, u); end if;

      b, wb := RandomWord (B);
      wb := PullbackWord (G, B, wb);
      v := y^b;
      S := sub < V | basis>;
      u := V! ((&cat[Eltseq (x): 
              x in &cat[Eltseq (ExtractBlock (v, 1, m + 1, m, d - 2 * m))]])
            cat 
      (&cat[Eltseq (x): 
         x in &cat[Eltseq (ExtractBlock (v, m + 1, d - m + 1, d - 2 * m, m))]]));
      if not u in S then Append (~I, b); Append (~wI, wb);
         Append (~basis, u); end if;

      S := sub < V | basis>;
       // "Dimensino (S) is ", Dimension (S);
   until S eq V or nmr gt Limit;

   if nmr gt Limit then error "Failed to span basis"; end if;

   M := MatrixAlgebra (F, Degree (V)) ! &cat[Eltseq (x): x in basis];
   return M, I, wI;
end function;

/* 
   A   X  Y   *  I   A^-1*X   U            A   0   * 
       I  Z            I      Z     =          I   0   
          A                   I                    A
             
     R       *        S              =        T

   We can construct R; we want to construct T as word;
   to do this we construct S and take product R * S to obtain T
*/

GeneralLinearProblem := function (G, C, m)

   d := Degree (G);
   K := BaseRing (G);

   A := KillFactor (G, C, [[1..m], [d - m + 1..d]], [[m + 1..d - m]] : 
                    Words := true);

   b := d - 2 * m;
   repeat 
      y, w := PullbackInvolution (G, A, [1..m]: SmallerCorank := true);
      // assert G`SLPGroupHom (w) eq y;

      /* construct element of form I  *  * by squaring y 
                                   0  I  *              
                                   0  0  I               */
      y := y^(2); w := w^2;
      X := ExtractBlock (y, 1, m + 1, m, b);
      Y := ExtractBlock (y, m + 1, d - m + 1, d - 2 * m, m);
   until Rank (X) gt 0 and Rank (Y) gt 0;

   B, _, WB := KillFactor (G, C, [[m + 1..d - m]], 
                  [[1..m], [d - m + 1..d]] : Words:=true, Parent := true);

   /* size of B block */
   b := d - 2 * m;
   X := ExtractBlock (y, 1, m + 1, m, b);
   Y := ExtractBlock (y, m + 1, d - m + 1, d - 2 * m, m);

   BlockVariations := function (a, wa, b, wb, m, A)
      x := a * b;
      X := ExtractBlock (x, 1, m + 1, m, d - 2 * m);
      if Rank (X) gt Rank (A) then
         return true, a * b, wa * wb, X;
      else
         return false, a, wa, A;
      end if;
   end function;

   /* construct element of corank m */
   while Rank (X) ne m do 
      a, wa := RandomWord (A);
      wa := PullbackWord (G, A, wa);
      b, wb := RandomWord (B);
      wb := PullbackWord (G, B, wb);
      flag, y, w, X := BlockVariations (y^a, w^wa, y^b, w^wb, m, X);
      Rank (X);
   end while;
   // assert G`SLPGroupHom (w) eq y;

   assert Rank (X) eq m;
     
   k := Degree (K);
   p := Characteristic (K);
   F := GF(p);

   V := VectorSpace (F, 2 * m * (d - 2 * m) * k);

   /* find spanning basis for V consisting of conjugates of y */
   M, I, wI := ObtainBasis (G, A, B, y, V, m);

   U := UserGenerators (A);
   W := UserWords (A);

   b := d - 2 * m;
   New := []; Word := [];

   for i in [1..#U] do 
      hold := U[i];
      whold := W[i];
      aa := ExtractBlock (hold, 1, 1, m,m);
      u := V! (
     (&cat[Eltseq (x): x in 
          &cat[Eltseq (aa^-1 * ExtractBlock ( hold, 1, m + 1, m, b))]])
     cat 
     (&cat[Eltseq (x): x in 
       &cat[Eltseq (ExtractBlock (hold, m + 1, d - m + 1, d - 2 * m, m))]])) ;
      flag, coords := IsConsistent (M, u);

      coords := [Integers ()! x : x in Eltseq (coords)];
      product := &*[(y^I[i])^coords[i]: i in [1..#coords]];
      wproduct := &*[(w^wI[i])^coords[i]: i in [1..#coords]];
      // assert G`SLPGroupHom (wproduct) eq product;

      /* now hold * product has both above-diagonal blocks cleared out */

      New[i] := hold * product;
      Word[i] := whold * wproduct;
   end for;

   return New, Word;
end function;
