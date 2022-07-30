forward ConstructInvolution;
forward Corank;

Variations := function (a, wa, b, wb, m: Equality := true)
   F := BaseRing (Parent (a));
   d := Nrows (a);
   MA := MatrixAlgebra (F, d);
   x := MA ! a + MA ! b;
   if Equality and Rank (x) eq m then
      return true, a * b, wa * wb;
   elif not Equality and Rank (x) gt Corank (a) then 
      return true, a * b, wa * wb;
   else
      return false, a, wa;
   end if;
end function;

/* extract section of A identified by action */ 
ExtractGroup := function (A, action)
   F := BaseRing (A);
   U := UserGenerators (A);
   U := [ExtractAction (U[i], action): i in [1..#U]];
   B := sub < GL(#action, F) | U>;
   B`UserGenerators := U;
   B`SLPGroup := A`SLPGroup;
   B`SLPGroupHom := MyHom (B, B`SLPGroup, B`UserGenerators);
   if assigned A`UserWords then B`UserWords := A`UserWords; end if;
   return B;
end function;

/* construct an involution in the section of X identified 
   by action; pull this involution back to parent G of X */

PullbackInvolution := function (G, X, action: ParentWord := true, 
              Small := true, SmallerCorank := false, Evaluation := true) 

   d := Degree (G); F := BaseRing (G);

t:= Cputime ();

   AX := ExtractGroup (X, action);
   inv, winv, cob := ConstructInvolution (AX: SmallerCorank := SmallerCorank);
INV := inv;
   winv := ImagesOfWords(AX, X, [winv]);
   winv := winv[1];
   S := Sections (X);
   degs := [Degree (x): x in S];

   m := Minimum (action) - 1;
   if Evaluation eq false then
      F := BaseRing (G);
      d := Degree (G);
      I := Identity (MatrixAlgebra (F, d));
      InsertBlock (~I, cob^-1 * inv * cob, m + 1, m + 1);
      inv := I;
   else 
      inv := X`SLPGroupHom (winv);
   end if;
   "Evaluate time in Pullback", Cputime (t);

   if ParentWord then winv := PullbackWord (G, X, winv); end if;
   return inv, winv;
end function;

Verify := function (G, E, W, CB)
   flag := [E[i] eq CB * G`SLPGroupHom (W[i]) * CB^-1: i in [1..#W]];
   return Set(flag) eq {true};
end function;

/* given an involution g of corank m, where w is its word in 
   user-generators of G, construct an involution of corank d div 2 */

CompleteConstruction := function (G, m, g, w)

   vprint Involution, 1: "Here in CompleteConstruction for Degree ", Degree (G);
   vprint Involution, 1: "At entry m is ", m;
  
   if IsIrreducible (G) eq false then error "Input is wrong reducible"; end if;

   d := Degree (G);
   F := BaseRing (G);

   cbi := InvolutionBaseChange (G, g);
   G := ApplyCOB (G, cbi);
   g := GL(d, F) ! (cbi * g * cbi^-1);

   C := CentraliserOfInvolution (G, g, w);
   h, wh, COB := FormulaElement (G, C, m);

   /* centraliser is A * *; 0 B *; 0 0 A;
      apply formula to construct A and B as SLs */
   A, B := FormulaAB (G, C, m, h, wh, COB);

   /* pull back involution from B */
   invB, winvB := PullbackInvolution (G, B, [m + 1 .. d - m]: 
                   Evaluation := false);

   "Corank of B is ", Corank (invB);

   M := d div 2;
   if Corank (invB) eq M then 
      return invB, winvB, COB * cbi; 
   end if;

   /* two involutions commute and sum of coranks is desired value */
   if Corank (g * invB) eq M then 
      return g * invB, w * winvB, COB * cbi; 
   else
      error "Product of these involutions has wrong corank";
   end if;

end function;
