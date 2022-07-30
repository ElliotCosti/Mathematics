Corank := function (g)
   d := Nrows (g);
   F := BaseRing (Parent (g));
   MA := MatrixAlgebra (F, d);
   return Rank (MA!g - Identity (MA));
end function;

/* apply change of basis matrix COB to G */

ApplyCOB := function (G, CB)
   U := UserGenerators(G);
   d := Degree (G);
   F := BaseRing (G);
   U := [GL(d, F) ! (CB * U[i] * CB^-1): i in [1..#U]];
   K := sub <GL(d, F) | U>;
   K`UserGenerators := U;
   K`SLPGroup := G`SLPGroup;
   K`UserWords := G`UserWords;
   K`SLPGroupHom := MyHom (K, K`SLPGroup, U);
   return K;
end function;

/* wg is word in generators of S which are words in generators of P;
   rewrite wg as word in generators of P */

PullbackWord := function (P, S, wg)
   theta := hom <Parent (wg) -> P`SLPGroup | S`UserWords>;
   wg := theta (wg);
   return wg;
end function;

/* possible ranks for smaller SL inside SL(d) in order 
   to construct involution of corank about d div 3 */

SelectRanks := function (d)
   if d in [2..4] then return [2]; end if;
   if d eq 14 then return [4, 5, 8, 9]; end if;
   if d gt 10 then
      range := [4 * d div 9 .. 5 * d div 9];
      range := [x : x in range | x mod 4 in {0, 1}];
      return range;
   end if;

   r := 1;
   range := [];
   repeat
      range cat:= [4 * r, 4 * r + 1];
      r +:= 1;
   until d - 4 * r lt 2;
   // if #range gt 1 then Prune (~range); end if;
   return range;

end function;

/* construct SL2 as subgroup of G and so obtain a corank 1 involution;
   now construct the derived group of its centraliser which has an SL2 
   section; find two elements in same Sylow 2-subgroup in SL2 and take 
   their commutator in G to obtain a rank 2 involution */

Degree4Involution := function (G: SmallerCorank := false)
   d := Degree (G);
   F := BaseRing (G);

   /* construct SL2 as subgroup and so obtain corank 1 involution */
   rank := [2];
   X, rank, COB := ConstructSmallerSL (G, rank);
   W := X`UserWords;

   R := ExtractGroup (X, [1..2]);
   R`UserWords := X`UserWords;
   R`SLPGroupHom := MyHom (R, R`SLPGroup, R`UserGenerators);

   nmr := 0;
   repeat 
      H := R;
      inv, w := ConstructInvolution (H : SmallerCorank := SmallerCorank);
      H`UserWords := W;
      w := PullbackWord (G, H, w);

      /* involution of rank 1 */
      inv := EvaluateWord (G, w);
      assert Order (inv) eq 2;

      /* now derived group of its centraliser */
      X := CentraliserOfInvolution (G, inv, w);
   
      Y := MyDerivedSubgroupWithWords (X);
      U := Y`UserWords;
      Y`UserWords := [PullbackWord (G, X, w): w in U];
 
      nmr +:= 1;
      /* construct SL2 = H as section */
      S := Sections (Y);
      
      flag := exists(i){i: i in [1..#S] | Degree (S[i]) eq 2
                        and MyIsLinearGroup (S[i])};
      if flag then 
         H := S[i];
         H`SLPGroup := Y`SLPGroup;
         H`UserWords := Y`UserWords;
         H`SLPGroupHom := MyHom (H, H`SLPGroup, H`UserGenerators);
         flag := RecognizeSL2 (H, #BaseRing (H): Verify := false);

         /* construct a and b in same Sylow 2-subgroup of H */
         a := SL(2, F) ! [1, 1, 0, 1];
         flag, wa := MySL2ElementToWord (H, a);
         wa := PullbackWord (G, H, wa);
         a := EvaluateWord (G, wa);
       
         b := SL(2, F) ! [1, F.1, 0, 1];
         flag, wb := MySL2ElementToWord (H, b);
         wb := PullbackWord (G, H, wb);
         b := EvaluateWord (G, wb);
   
         /* expect commutator to be a corank 2 involution */
         inv := (a, b);
      end if;
   until Corank (inv) eq 2;
  
   vprint Involution, 1: "Degree 4: trial ", nmr, "found corank 2";
   winv := (wa, wb);

   return inv, winv, Identity (G);
end function;

/* find involution of corank equal to rank div 2 in SL (d, q);
   first construct SL(rank, q) as subgroup of SL(d, q) 
   and now pull back involution from this smaller SL */

SmallCorankInvolution := function (G, rank: SmallerCorank := false)
   X, m, CB := ConstructSmallerSL (G, rank);
   inv, w := PullbackInvolution (G, X, [1..m]: 
             Evaluation := false, SmallerCorank := SmallerCorank);
   return inv, w, CB;
end function;

/* construct involution of corank d div 2 in G = SL(d, q) */

ConstructInvolution := function (G: Scalars := false, SmallerCorank := false)

   if Degree (G) gt 2 then 
      U := UserGenerators (G);
      _ := InitialiseGroup (G: scalars := Scalars, generators := U);
   end if;

   d := Degree (G);
   F := BaseRing (G);
   if Characteristic (F) ne 2 then error "For even char only"; end if;
   if d eq 2 then 
      inv := GL(d, F)![1,1,0,1];
      T := CompositionTree (G: KnownLeaf := true);
      flag, w := SolveWord (T, T[1], inv); 
      assert flag eq true;
      return inv, w, Id (G);
   elif d eq 3 then 
       rank := [2];
       return SmallCorankInvolution (G, rank: SmallerCorank := SmallerCorank);
   elif d eq 4 then 
      return Degree4Involution (G: SmallerCorank := SmallerCorank);
   elif d eq 5 then
      rank := [4];
      return SmallCorankInvolution (G, rank: SmallerCorank := SmallerCorank);
   else
      ranks := SelectRanks (d);
      inv, w, CB := SmallCorankInvolution (G, ranks:SmallerCorank := SmallerCorank);
      m := Corank (inv);
      if SmallerCorank eq false then 
         H := ApplyCOB (G, CB);
         inv, w, cb := CompleteConstruction (H, m, inv, w);
      else 
         cb := Identity (G);
      end if;
      return inv, w, cb * CB; 
   end if;
end function;
