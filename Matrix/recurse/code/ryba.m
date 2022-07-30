forward ConjugateToKnownInvolution; 
forward ClassicalRyba;

BrayGeneratorsWords := function (G, g, wg: fct := Order)
   repeat 
      h, wh := RandomWord (G);
   until h^2 ne Identity (G);
   c := (g, h);
   o := fct (c);
   m := o div 2;
   if IsEven (o) then 
      return [c^m, (g, h^-1)^m], [(wg, wh)^m, (wg, wh^-1)^m]; 
   else 
      return [h * c^m], [wh * (wg, wh)^m];
   end if;
end function;

/* find odd order generators if possible */

OddBrayGeneratorsWords := function (G, g, wg: Limit := 50, fct := Order)
   nmr := 0;
   repeat 
      nmr +:= 1;
      repeat 
         h, wh := RandomWord (G);
      until h^2 ne Identity (G);
      c := (g, h);
      o := fct (c);
      m := o div 2;
      if IsOdd (o) then 
         return true, [h * c^m], [wh * (wg, wh)^m];
      end if;
   until nmr eq Limit;
   return false, _, _;
end function;

/* g involution in G; wg is corresponding word; 
   construct its centraliser */

CentraliserOfInvolution := function (G, g, wg: fct := Order, N := 5, Nmr := 10)

   S := G`SLPGroup;
   F := BaseRing (G);
   d := Degree (G);
   lambda := UserGenerators (G)[1];
   E := [[lambda], [g]]; W := [[S.1], [wg]];

   for i in [3..N + 2] do
      flag, E[i], W[i] := OddBrayGeneratorsWords (G, g, wg: fct := fct);
      if not flag then 
         "No odd Bray generators found";
         E[i], W[i] := BrayGeneratorsWords (G, g, wg: fct := fct);
      end if;
   end for;
   vprint User1: "Lengths are ", [#e: e in E];
   E := &cat(E);
   assert Position (E, g) eq 2;
   W := &cat(W);

   PG := RandomProcess (G);
   R :=  SetToSequence (Set(&cat[BrayGenerators (PG, g): i in [1..Nmr]]));

   C := sub < GL(d, F) | E>;
   C`UserGenerators := E;
   C`UserWords := W;

   B := SLPGroup (#E);
   C`SLPGroup := B;
   C`SLPGroupHom := MyHom (C, B, E);

   C`RandomElements := R;
   return C;

end function;

InitialiseGroup := function (G: scalars := true, generators := [], words := [])
   if generators eq [] then generators := [G.i : i in [1..Ngens (G)]]; end if;
   d := Degree (G);
   if Type (G) eq GrpMat then
      F := BaseRing (G);
      L := GL(d, F);
   elif Type (G) eq GrpPerm then
      L := Sym (d);
   else
      L := G;
   end if;

   if scalars then 
      U := [L ! Identity (G)] cat generators;
   else 
      U := generators;
   end if;
   G`UserGenerators := U;
   n := #U;
   B := SLPGroup (n);
   G`SLPGroup := B;
   G`SLPGroupHom := MyHom (G, B, U);
   if words eq [] then 
   G`UserWords := [B.i : i in [1..n]];         
   else 
   G`UserWords := words;
   end if;
   G`CentraliserTrees := [];
   return true;
end function;

CI := CentraliserOfInvolution; 

/* we have only a subgroup C of the centraliser in G of g;
   add in new generator to C */

AddCentraliserGenerator := function (G, C: fct := Order)

   g := C`UserGenerators[2]; 
   wg := C`UserWords[2]; 
   assert fct (g) eq 2;

   flag, h, wh := OddBrayGeneratorsWords (G, g, wg: fct := fct);
   if not flag then 
      h, wh := BrayGeneratorsWords (G, g, wg: fct := fct);
   end if;
   E := C`UserGenerators cat h;
   W := C`UserWords cat wh;

   F := BaseRing (G);
   d := Degree (G);
   D := sub < GL(d, F) | E>;

   B := SLPGroup (#E);
   D`SLPGroup := B;
   D`SLPGroupHom := MyHom (D, B, E);

   D`UserGenerators := E;
   D`UserWords := W;
   D`RandomElements := C`RandomElements;

   return D;

end function;

/* construct centraliser of involution of g having word wg in G */

ConstructCentraliser := function (G, g, wg: KernelRank := 10, fct := Order)
   flag, T, x, wx := ConjugateToKnownInvolution (G, g, wg: fct := fct);
   if flag then return T, x, wx; end if;

   C := CI (G, g, wg: fct := fct);
   S := G`SLPGroup;

   d := Degree (G);
   F := BaseRing (G);

tt := Cputime ();
   T := CompositionTree (C : KernelRank := KernelRank, RandomElts := C`RandomElements);
   while Type (T) eq BoolElt do
      C := AddCentraliserGenerator (G, C);
      T := CompositionTree (C : KernelRank := KernelRank, RandomElts := C`RandomElements);
   end while;

"Time to solve centraliser structure", Cputime (tt);
    
   if not assigned G`CentraliserTrees then G`CentraliserTrees := []; end if;
   Append (~G`CentraliserTrees, <GL (d, F) ! g, wg, T>); 
   return T, Identity (G), Identity (S);
   
end function;

/* Dihedral trick: 
   if a^2 = b^2 = 1, and b * a = c has odd order 2n + 1,
   then c^-n * a * c^n = b

   if b * a does not have odd order, then choose random 
   conjugate a^x of a such that b * a^x = c has odd order; 
   now conjugate from a -> a^x -> b */

ConjugateInvolutions := function (G, a, b: fct := Order, Limit := 50)

   c := b * a;
   o := fct (c);
   if IsOdd (o) then 
      n := o div 2;
      return true, c^n;
   end if;

   /* addition: if Order (a * b) eq 2 then Add b to Centraliser a */

   P := RandomProcess (G);
   nmr := 0;
   repeat
      x := Random (P);
      c := b * a^x;
      o := fct (c);
      nmr +:= 1;
   until (IsOdd (o) or nmr eq Limit);

   if IsOdd (o) then 
      n := o div 2;
      assert a^(x * c^n) eq b;
      return true, x * c^n;
   else 
      return false, _;
   end if;

end function;

/* Dihedral trick: 
   if a^2 = b^2 = 1, and b * a = c has odd order 2n + 1,
   then c^-n * a * c^n = b

   if b * a does not have odd order, then choose random 
   conjugate a^x of a such that b * a^x = c has odd order; 
   now conjugate from a -> a^x -> b */

ConjugateInvolutionsWords := function (G, a, wa, b, wb: 
                          fct := Order, Limit := 50, NmrFound := 10)

   c := b * a;
   o := fct (c);
   if IsOdd (o) then 
      n := o div 2;
      return true, c^n, (wb * wa)^n;
   end if;

   /* take known conjugate and see how 
      many times we find it */
   r := Random (G); y := a^r; found := 0;

   nmr := 0;
   repeat
      x, wx := RandomWord (G);
      c := b * a^x;

      d := y * a^x;
      if IsOdd (fct (d)) then found +:= 1; end if;
      
      o := fct (c);
      nmr +:= 1;
   until (IsOdd (o) or found eq NmrFound or nmr eq Limit);

   // "found = ", found; "nmr = ", nmr;
   if IsOdd (o) then 
      n := o div 2;
      assert IsDiagonal (a^(x * c^n) * b^-1);
      return true, x * c^n, wx * (wb * wa^wx)^n;
   else 
      return false, _, _;
   end if;

end function;

/* g^x may be an element of Z[1], a subgroup of H;
   if so, write g as a word in generators of H */

WriteElement := function (H, Z, g, x, wx)
   flag, wg := SolveWord (Z, Z[1], g^x);
   if flag then 
      delta := Z[1]`group`SLPGroupHom;
      // assert IsScalar (delta (wg) * g^-1);
      P := H`SLPGroup;
      theta := hom <Parent (wg) -> P | GroupOfNode (Z[1])`UserWords>;
      wg := theta (wg);
      wg := wx * wg * wx^-1;
      delta := H`SLPGroupHom;
      assert IsScalar (delta (wg) * g^-1);
      return true, wg;
   else 
      return false, _;
   end if;
end function;

/* is g conjugate to known involution i? if so,
   compute x so that i = g^x, return centraliser 
   of i, x and word for x */

ConjugateToKnownInvolution := function (H, g, wg: fct := Order)
   Trees := CentraliserTrees (H);
   if Trees cmpeq false then return false, _, _, _; end if;
   Inv := [Trees[i][1]:  i in [1..#Trees]];
   W := [Trees[i][2]:  i in [1..#Trees]];
   for j in [1..#Inv] do 
      found, x, wx := ConjugateInvolutionsWords 
                    (H, g, wg, Inv[j], W[j]: fct := fct); 
      if found then return true, Trees[j][3], x, wx; end if;
   end for;
         
   return false, _, _, _;

end function;

AlternativeSolution := function (H, g)
   "USE SLPImage directly -- order of H is ", #H;
   SetupMatrixLeaf (H);
   flag, w := SLPImage (H, g);
   return flag, w;
end function;

/* implementation of Ryba strategy for membership testing;
   given H subgroup of G, decide if g an element of G is
   also element of H  */

Ryba := function (H, g : fct := Order, Verify := false, 
                         LIMIT := 100, Direct := false)

   if RecognizeClassical (H) then 
      if ClassicalType (H) eq "symplectic" and Degree (H) eq 4 
         then fct := ProjectiveOrder; 
      end if;
      return ClassicalRyba (H, g: Verify := Verify, LIMIT := LIMIT, 
                            fct := fct, Direct := Direct);
   end if;

   if Direct then _ := InitialiseGroup (H); end if; 

   if IsIdentity (g) or Ngens (H) eq 0 then 
      return true, Identity (H`SLPGroup);
   end if;

   /* find h such that g * h has order 2 ell */
   nmr := 0;
   repeat 
      h, wh := RandomWord (H);
      o := fct (g * h);
      nmr +:= 1;
   until IsEven (o) or nmr gt LIMIT;

   "order of g is ", Order (g);
   if nmr gt LIMIT then 
      "order of g is ", Order (g);
      return AlternativeSolution (H, g); 
   end if;
  
   ell := o div 2;
   gh := g * h;
   z := (gh)^(ell);

   /* find t an H-involution, distinct from z */
   nmr := 0; L := LIMIT div 10;
   repeat 
      t, wt := ElementOfOrder (H, 2, 50: Word := true, Fct := fct);
      nmr +:= 1;
      complete := (t cmpeq false) or (z ne t) or (nmr eq L);
   until complete;
   
   if t cmpeq false or z eq t then 
      "part II: order of g is ", Order (g);
      return AlternativeSolution (H, g); 
   end if;

   // if z eq t then error "z = t"; end if;

   /* find a random H-conjugate of z 
      such that z * t has order 2m */
   nmr := 0;
   repeat 
      a, wa := RandomWord (H);
      o := fct (z^a * t);
      nmr +:= 1;
   until IsEven (o) or nmr gt LIMIT;

   if nmr gt LIMIT then 
      "part III: order of g is ", Order (g);
      return AlternativeSolution (H, g); 
   end if;

   m := o div 2;
   z := z^a; 
   y := (z * t)^(m);

   /* construct centraliser T of t in H and decide
      if y is in T */
   T, x, wx := ConstructCentraliser (H, t, wt: fct := fct);

   if Verify then 
      "order of t-centraliser is ", #T[1]`group;
      // assert #T[1]`group eq #Centraliser (H, t); 
   end if;

   flag, wy := WriteElement (H, T, y, x, wx);
   if not flag then return false, _; end if;

   /* construct centraliser Y of y in H and decide
      if z is in Y */
   Y, x, wx := ConstructCentraliser (H, y, wy: fct := fct);

   if Verify then 
      "order of y-centraliser is ", #Y[1]`group;
      // assert #Y[1]`group eq #Centraliser (H, y); 
   end if;

   flag, wz := WriteElement (H, Y, z, x, wx);
   if not flag then return false, _; end if;

   /* construct centraliser Z of z in H and decide
      if g * h is in Z */
   Z, x, wx := ConstructCentraliser (H, z, wz: fct := fct);

   if Verify then 
      "order of z-centraliser is ", #Z[1]`group;
       // assert #Z[1]`group eq #Centraliser (H, z); 
   end if;

   gh := gh^a;
   flag, wgh := WriteElement (H, Z, gh, x, wx);
   if not flag then return false, _; end if;

   delta := H`SLPGroupHom;
   wg := wa * wgh * wa^-1 * wh^-1;
   assert IsScalar (delta (wg) * g^-1);

   return true, wg;

end function; 

RandomElementsSatisfyLeaf := function (node)
   G := GroupOfNode (node);
   R := G`RandomElements;
   flag := IsRybaGroup (G);
   vprint User1: "Use involution centraliser strategy to solve word problem? ", flag;
   if flag eq true then fct := Ryba; else fct := SLPImage; end if;
   if IsRybaGroup (G) eq true then fct := Ryba; 
   elif IsSL2Group (G) cmpeq true then fct := MySL2ElementToWord; 
   elif Type (G) eq GrpAb then fct := SolveWordCyclicGroup;
   else fct := SLPImage; end if;
   if (exists (x) {x : x in R | fct (G, x) cmpeq false}) then
      vprint User2:
      "NOW Random element failed membership test for leaf -- crisis";
      return false;
   else
      return true;
   end if;

end function;
