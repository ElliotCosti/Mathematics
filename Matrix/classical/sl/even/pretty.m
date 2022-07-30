EvaluatePoly := function (F, f, A)
   c := Coefficients (f);
   B := &+[c[i] * A^(i - 1): i in [1..#c]];
   return Nullspace (B);
end function;

EvaluationAction := function (d, F, facs, A)
   U := [EvaluatePoly (F, facs[i], A): i in [1..#facs]];
   B := &cat[[Eltseq (u): u in Basis (U[i])]: i in [1..#U]];
   B := &cat (B);
   CB := GL (d, F) ! B;
   return CB * A * CB^-1;
end function;

InvestigatePair := function (G, L, R, W, rank, sum) 
   F := BaseRing (G);
   d := Degree (G);
   j := #R;
   
   for i in [1..#R - 1] do 
      if R[i] + R[j] in sum then
         expected := 2 * d - (R[i] + R[j]);
         ax := L[i]; ay := L[j]; 
         H := sub < GL(d, F) | ax, ay>;
         _ := InitialiseGroup (H);
         S := Sections (H);
          "Dimensions found are ", [Degree (s): s in S];
         if exists (x) {x : x in S | Degree (x) eq expected and
                                     MyIsLinearGroup (x)} then
            wx := W[i]; wy := W[j];
            H`UserWords := [wx^0, wx, wy];
            return true, H, Degree (x); 
         end if;
      end if;
   end for;

   return false, _, _; 
end function;

/* action of g on factor of f having degree m */

ActionOnFactor := function (G, g, w, m, fac)
   d := Degree (G);
   F := BaseRing (G);
   MA := MatrixAlgebra (F, d);
   Sort (~fac);
   Reverse (~fac);
   g := MA ! g;
   h := EvaluationAction (d, F, fac, g);
   B := ExtractBlock (h, 1, 1, m, m);
   o := ProjectiveOrder (B: Proof := false);
   return g^o, w^o, B^o;
end function;

FindElement := function (G, range: Limit := 100)
   d := Degree (G);
   nmr := 0;
   repeat
      g, w := RandomWord (G);
      f := CharacteristicPolynomial (g);
      fac := Factorisation (f);
      fac := [fac[i][1] : i in [1..#fac]];
      deg := [Degree (f): f in fac];
      degs := Set (deg);
      m := Maximum (degs);
      if &+degs eq d and m in range then 
         x, w := ActionOnFactor (G, g, w, m, fac);
         if not IsDiagonal (x) then 
             return x, w, m, nmr;
         end if;
      end if;
      nmr +:= 1;
      if nmr mod 20 eq 0 then "FindElement ...", nmr; end if;
   // until nmr gt Limit;
   until nmr lt 0;

   return false, _, _, _;

end function;
  
/* find SL(d, e) as subgroup of SL(d, q) for some e in rank */

SmallerSL := function (G, rank: Limit := 1000, Words := true) 

   L := []; R := []; W := [];
   e := Maximum (rank);
   d := Degree (G);
   range := [d - e + 1..d - 1];
   sum := [2 * d - e: e in rank]; 
   // "rank is ", rank; "range is", range; "sum is ", sum;

   total := 0;
   for i in [1..Limit] do 
      if i mod 20 eq 0 then  "select element", i; end if;
      L[i], W[i], R[i], tot := FindElement (G, range); 
      found, H, e := InvestigatePair (G, L, R, W, rank, sum);
      total +:= tot;
      if found then 
         "Tested ", i, "elements to find SL of rank", e; 
         "We considered ", total , "elements";
         return H, e; 
      end if;
   end for;

   if not found then error "failed to find suitable pair"; end if;
end function;

/* ensure we can see SL(m, q) as top-left hand block of G */

MakePretty :=  function (G, m: Limit := 100)

   S := Sections (G);
   CB := G`ChangeOfBasis;
   degs := [Degree (S[i]): i in [1..#S]];
   index := Position (degs, m);
   other := Rep ([x : x in [1..#S] | x ne index]);

   F := BaseRing (G);
   d := Degree (G);
   MA := MatrixAlgebra (F, d);
   V := VectorSpace (F, d);

   /* first space is union of alpha image spaces: y - alpha_y I 
     where y runs over generating set;
     second space is intersection of alpha eigen spaces */

   E := [* *]; U := [* *];
   for i in [1..Ngens (G)] do
      B := MatrixBlocks (G, G.i);
      alpha := B[other][1][1];
      es := Eigenspace (G.i, alpha);
      E[i] := es;
      N := ScalarMatrix (d, -alpha);
      U[i] := (G.i - N);
   end for;
   E := [x : x in E];
   E := &meet (E);
   Y := &cat[[U[j][i] : i in [1..d]]: j in [1..#U]];
   S := sub < V | Y >;
   B := Basis (S); BE := Basis (E);
   T := [B[i] : i in [1..#B]] cat [BE[i] : i in [1..#BE]];
   CB := MA ! &cat [Eltseq (t): t in T];
   
   return CB;
 
end function;

/* construct SL_m as subgroup of G and perform change of basis
   to exhibit it as top-left corner of G */

ConstructSmallerSL := function (G, rank)

   d := Degree (G);
   H, m := SmallerSL (G, rank);
   CB := MakePretty (H, m);
   H := ApplyCOB (H, CB);
   Blist := [[i] : i in [m + 1..d]];
   H := KillFactor (G, H, [[1..m]], Blist: Words := true);
   return H, m, CB;
end function;
