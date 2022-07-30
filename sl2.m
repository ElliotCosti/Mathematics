freeze;

// SetVerbose ("RandomSchreier", 2);
// SetVerbose ("STCS", 2);

declare verbose sl2q, 1;

forward MySL2ElementToWord;

import "../Smash/functions.m": TensorProductFlag;
import "../Tensor/is-tensor.m": TensorDimensions;

import "natural.m": ConstructSL2Basis;
import "decompose.m": DecomposeTensor, ScaledTensorFactors, 
                      ScaleFactor, ScalarMultiple, ScaleMatrix;
import "issympower.m": IsSymmetricPower, PreimageOfElement;
import "ldu.m": SL2ElementToSLP;
import "large-to-small.m": LargeToSmall, SmallToLarge;

intrinsic RandomConjugate (G :: GrpMat) -> GrpMat 
{return random conjugate of G}
   P := GL (Degree (G), BaseRing (G));
   x := Random (P);
   return G^x;
end intrinsic;

/* set up hom from B -> G where U is the list of images of
   generators of B; do it in this way to  ensure that it
   does not force membership testing in G */

MyHom := function (G, B, U)
   d := Degree (G);
   if Type (G) eq GrpMat then 
      F := BaseRing (G);
      P := GL (d, F);
   elif Type (G) eq GrpPerm then 
      P := Sym (d);
   end if;
   gens := [P ! G.i : i in [1..Ngens (G)]];
   pos := [Position (gens, U[i]) : i in [1..#U]];
   return hom <B -> G | [G.i : i in pos]>;

end function;

HasCorrectShape := function (X, i, j)
   return (X[1][1] eq 1) and (X[2][2] eq 1) and
          (X[j][i] eq 0) and (X[i][j] ne 0);
end function;

/* upper triangular, lower triangular and diagonal matrices required */
  
IsSL2Basis := function (gens)

   if Nrows (Rep (gens)) ne 2 then 
      return false, _, _, _;
   end if;

   if forall{x : x in gens | Determinant (x) ne 1} then 
      return false, _, _, _;
   end if;

   if #gens ne 3 then return false, _, _, _; end if;

   if not exists (DM) {x : x in gens | IsDiagonal (x)} then 
      return false, _, _, _;
   end if;

   if not exists (LM) {x : x in gens | HasCorrectShape (x, 2, 1)} then 
      return false, _, _, _;
   end if;

   if not exists (UM) {x : x in gens | HasCorrectShape (x, 1, 2)} then 
      return false, _, _, _;
   end if;

   return true, DM, LM, UM;
end function;

SL2Basis := function (G)
   if assigned G`SL2Basis then return G`SL2Basis; else return false; end if;
end function;

procedure SetSL2Basis (G, Basis)
   G`SL2Basis := Basis; 
end procedure;

/* recognize SL(2, q) */

MyRecognizeSL2 := function (H) 

   if Degree (H) eq 2 then 
      flag := RecogniseClassical (H);
      if flag and IsProbablyPerfect (H) then 
         flag := ConstructSL2Basis (H);
         if flag then 
            return true;
         else
            return false;
         end if;
      else
         return false;
      end if;
   end if;

"NOW HERE";
   flag, CB := DecomposeTensor (H);
   if flag eq true then 
      First, Second := ScaledTensorFactors (H, CB);
      if Type (First) eq BoolElt then return false; end if;
   else 
      First := H;
   end if;

   if Degree (First) eq 2 then 
      N := First;
      cb := Identity (N);
      gens := UserGenerators (N);
   else 
      flag, cb, gens := IsSymmetricPower (First);
      if not flag and assigned Second then 
         flag, cb, gens := IsSymmetricPower (Second);
      end if;
      if not flag then return false; end if;
      K := BaseRing (H);
      N := sub <GL (2, K) | gens>;
      N`UserGenerators := gens;
   end if;

   if assigned H`SLPGroup then 
      N`SLPGroup := H`SLPGroup; 
      N`SLPGroupHom := MyHom (N, N`SLPGroup, gens);
   end if;
"HERE";

   flag := ConstructSL2Basis (N);
   if flag eq false then return false; end if;

   /* add into B the change-of-basis matrix for the symmetric power */
   B := SL2Basis (N);
   SetSL2Basis (H, <B[1], B[2], B[3], cb>);

   return true;
end function;

intrinsic RecogniseSL2(G::GrpMat, q::RngIntElt: Verify := true) -> BoolElt, Map, Map, Map, Map 
{G is absolutely irreducible matrix group defined
 modulo scalars over minimal finite field F; 

 if G is isomorphic, possibly modulo scalars, to (P)SL(2, q),
 where F and GF(q) have the same characteristic, construct 
 homomorphisms between G and (P)SL(2, q);

 return homomorphism from G to (P)SL(2, q), homomorphism
 from (P)SL(2, q) to G, and, where known, the map from G to
 its word group and the map from the word group to G;

 if Verify is false, then assume G is absolutely irreducible
 and defined modulo scalars over minimal field, otherwise 
 check that these conditions hold.}

   F := BaseRing (G);
   p := Characteristic (F);

   f := Factorization (q);
   require #f eq 1: "Argument 2 must be a prime power";

   require p eq f[1][1]: 
      "Defining characteristic must equal characteristic of input";
   e := f[1][2];

   d := Degree (G);

   /* special cases */
   if (IsOdd (p) and ((e eq 2 and d in {(p - 1)^2, p * (p - 1)}) or
                (d eq p^e))) or (q in [2, 3]) then  
      flag, phi, tau := RecogniseSL (G, 2, q);
      if flag then "No word maps available"; return flag, phi, tau, _, _; 
      else return flag, _, _, _, _; end if;
   end if;

   if Verify then 
      if not IsAbsolutelyIrreducible (G) then 
         "Input group must be absolutely irreducible"; 
         return false, _, _, _, _;
      end if;
      if #F gt q then       
         flag := IsOverSmallerField (G : Scalars := true); 
         if flag eq true then 
            "Input group must be over minimal field modulo scalars";
            return false, _, _, _, _;
         end if;
      end if;
   end if;

   if #F lt q then 
      printf "To apply RecognizeSL2 to G, first embed G in GL(%o, %o^%o)\n", d, p, e;
      return false, _, _, _, _;
   end if;

   flag := MyRecognizeSL2 (G);
   if not flag then return false, _, _, _, _; end if;

   H := SL(2, q);
   forw := hom<G -> H | x :-> LargeToSmall (G, x)>;
   back := hom<H -> G | x :-> SmallToLarge (G, x)>;

   w := MySL2ElementToWord (G, G.1);
   W := Parent (w);
   word := hom<G -> W | x :-> MySL2ElementToWord (G, x)>;
   delta := G`SLPGroupHom;

   return true, forw, back, word, delta;
end intrinsic;

intrinsic RecogniseSL2 (G::GrpMat, q ::RngIntElt: Verify := true) -> BoolElt, Map, Map, Map, Map 
{G is absolutely irreducible matrix group defined
 modulo scalars over minimal finite field F; 

 if G is isomorphic, possibly modulo scalars, to (P)SL(2, q),
 where F and GF(q) have the same characteristic, construct 
 homomorphisms between G and (P)SL(2, q);

 return homomorphism from G to (P)SL(2, q), homomorphism
 from (P)SL(2, q) to G, and, where known, the map from G to
 its word group and the map from the word group to G;

 if Verify is false, then assume G is absolutely irreducible
 and defined modulo scalars over minimal field, otherwise 
 check that these conditions hold.}

   F := BaseRing (G);
   p := Characteristic (F);

   f := Factorization (q);

   if (p ne f[1][1]) then 
      "Defining field size must equal characteristic of input";
      return false;
   end if;
   e := f[1][2];

   d := Degree (G);

   /* special cases */
   if (IsOdd (p) and ((e eq 2 and d in {(p - 1)^2, p * (p - 1)}) or
                 (d eq p^e))) or (q in [2, 3]) then  
      flag, phi, tau := RecogniseSL (G, 2, q);
      if flag then 
         "No word maps available"; return flag, phi, tau, _, _; 
      else 
         return flag, _, _, _, _; 
      end if;
   end if;

   if Verify and not IsAbsolutelyIrreducible (G) then 
      "Input group must be absolutely irreducible"; 
      return false, _, _, _, _;
   end if;

   if Verify or #F gt q then 
      flag := IsOverSmallerField (G : Scalars := true); 
      if flag eq true then 
         "Input group must be over minimal field modulo scalars";
         return false, _, _, _, _;
      end if;
   end if;

   P := GL(d, p^e);
   if #F lt q then 
      vprintf sl2q:"To apply RecognizeSL2 to G, first embed G in GL(%o, %o^%o)\n", d, p, e;
      U := [P!u: u in UserGenerators (G)];
      M := sub <P| U>;
      M`UserGenerators := U;
      new := true;
   else
      M := G;
      new := false;
   end if;

   flag := MyRecognizeSL2 (M);
   if not flag then return false, _, _, _, _; end if;

   /* may need to record data from M */
   if new then 
      G`SL2Basis := M`SL2Basis;
      if TensorProductFlag (M) cmpeq true then 
         CB := TensorBasis (M);
         facs := TensorFactors (M);
         G`TensorProductFlag := true; 
         G`TensorBasis := CB;
         G`TensorFactors := facs;
      end if;
   end if;

   H := SL(2, q);
   forw := hom<P -> H | x :-> LargeToSmall (M, x)>;
   gl := GL(Degree (G), F);
   back := hom<H -> gl | x :-> SmallToLarge (M, x)>;

   w := MySL2ElementToWord (M, M.1);
   W := Parent (w);
   word := hom<P -> W | x :-> MySL2ElementToWord (M, x)>;
   delta := MyHom (G, W, UserGenerators (G));
   return true, forw, back, word, delta;
end intrinsic;

intrinsic RecogniseSL2 (G::GrpMat: Verify := true) -> BoolElt, Map, Map, Map, Map 
{G is absolutely irreducible matrix group defined
 modulo scalars over minimal finite field F; 

 if G is isomorphic, possibly modulo scalars, to (P)SL(2, q),
 where F and GF(q) have the same characteristic, construct 
 homomorphisms between G and (P)SL(2, q);

 return homomorphism from G to (P)SL(2, q), homomorphism
 from (P)SL(2, q) to G, and, where known, the map from G to
 its word group and the map from the word group to G;

 if Verify is false, then assume G is absolutely irreducible
 and defined modulo scalars over minimal field, otherwise 
 check that these conditions hold.}

   F := BaseRing (G);
   p := Characteristic (F);

   if Verify and not IsAbsolutelyIrreducible (G) then 
      vprintf sl2q:"Input group must be absolutely irreducible"; 
      return false, _, _, _, _;
   end if;

   /* field size subject to assumption G is (P)SL(2) */
   k, q := SL2Characteristic (G);
   if k eq 0 or q eq 0 then 
      "Input is not (P)SL(2) in characteristic ", p; 
      return false, _, _, _, _;
   else
      vprint sl2q:"Defining field has size ", q;
   end if;

/* 
   flag, name := LieType (G, p);
   if (flag eq false) or (flag eq true and (name[1] ne "A" or name[2] ne 1)) then 
      "Input is not SL(2) in characteristic ", p; 
      return false, _, _, _, _;
   end if;
   q := name[3];
*/
   
   f := Factorization (q);

   if (p ne f[1][1]) then 
      "Defining characteristic must equal characteristic of input";
      return false;
   end if;

   e := f[1][2];

   d := Degree (G);

   /* special cases */
   if (IsOdd (p) and ((e eq 2 and d in {(p - 1)^2, p * (p - 1)}) or
                 (d eq p^e))) or (q in [2, 3]) then  
      flag, phi, tau := RecogniseSL (G, 2, q);
      if flag then 
         "No word maps available"; return flag, phi, tau, _, _; 
      else 
         return flag, _, _, _, _; 
      end if;
   end if;

   if Verify or #F gt q then 
      flag := IsOverSmallerField (G : Scalars := true); 
      if flag eq true then 
         "Input group must be over minimal field modulo scalars";
         return false, _, _, _, _;
      end if;
   end if;

   P := GL(d, p^e);
   if #F lt q then 
      vprintf sl2q:"To apply RecognizeSL2 to G, first embed G in GL(%o, %o^%o)\n", d, p, e;
      U := [P!u: u in UserGenerators (G)];
      M := sub <P| U>;
      M`UserGenerators := U;
      new := true;
   else
      M := G;
      new := false;
   end if;

   flag := MyRecognizeSL2 (M);
   if not flag then return false, _, _, _, _; end if;

   /* may need to record data from M */
   if new then 
      G`SL2Basis := M`SL2Basis;
      if TensorProductFlag (M) cmpeq true then 
         CB := TensorBasis (M);
         facs := TensorFactors (M);
         G`TensorProductFlag := true; 
         G`TensorBasis := CB;
         G`TensorFactors := facs;
      end if;
   end if;

   H := SL(2, q);
   forw := hom<P -> H | x :-> LargeToSmall (M, x)>;
   gl := GL(Degree (G), F);
   back := hom<H -> gl | x :-> SmallToLarge (M, x)>;

   w := MySL2ElementToWord (M, M.1);
   W := Parent (w);
   word := hom<P -> W | x :-> MySL2ElementToWord (M, x)>;
   delta := MyHom (G, W, UserGenerators (G));
   return true, forw, back, word, delta;
end intrinsic;

intrinsic RecognizeSL2(G::GrpMat, q::RngIntElt: Verify := true) -> BoolElt, Map, Map, Map, Map 
{G is absolutely irreducible matrix group defined
 modulo scalars over minimal finite field F; 

 if G is isomorphic, possibly modulo scalars, to (P)SL(2, q),
 where F and GF(q) have the same characteristic, construct 
 homomorphisms between G and (P)SL(2, q);

 return homomorphism from G to (P)SL(2, q), homomorphism
 from (P)SL(2, q) to G, and, where known, the map from G to
 its word group and the map from the word group to G;

 if Verify is false, then assume G is absolutely irreducible
 and defined modulo scalars over minimal field, otherwise 
 check that these conditions hold.}

   return RecogniseSL2(G, q: Verify := Verify);

end intrinsic;

intrinsic RecognizeSL2(G::GrpMat: Verify := true) -> BoolElt, Map, Map, Map, Map 
{G is absolutely irreducible matrix group defined
 modulo scalars over minimal finite field F; 

 if G is isomorphic, possibly modulo scalars, to (P)SL(2, q),
 where F and GF(q) have the same characteristic, construct 
 homomorphisms between G and (P)SL(2, q);

 return homomorphism from G to (P)SL(2, q), homomorphism
 from (P)SL(2, q) to G, and, where known, the map from G to
 its word group and the map from the word group to G;

 if Verify is false, then assume G is absolutely irreducible
 and defined modulo scalars over minimal field, otherwise 
 check that these conditions hold.}

   return RecogniseSL2(G: Verify := Verify);

end intrinsic;

/* write g as word in user-generators of G */

MySL2ElementToWord := function (G, g) 

   Basis := SL2Basis (G);
   if Type (Basis) eq BoolElt then 
      error "First apply RecogniseSL2"; 
   end if;
   dim2cb := Basis[3]; cb := Basis[4];

   K := BaseRing (Parent (cb));
   g := GL(Degree (G), K) ! g;

   if TensorProductFlag (G) cmpeq true then 
      CB := TensorBasis (G);
      u, w := TensorDimensions (G);
      flag, facs := IsProportional (g^CB, u);
      if flag then h := GL(u, K) ! facs[1]; else return false, _; end if;
      det := Determinant (h);
      flag, lambda := IsPower (det, u);
      if not flag then return false, _; end if;
      h := GL (u, K) ! ScalarMultiple (h, lambda^-1);
      P := TensorFactors (G)[1];
      P := ScaleFactor (P);
   else 
      h := g;
      P := G;
   end if;

   flag, n := PreimageOfElement (P, cb * h * cb^-1, cb);
   if flag eq false or Determinant (n) ne 1 then return false, _; end if;

   w := SL2ElementToSLP (G, dim2cb * n * dim2cb^-1);
   if Type (w) eq BoolElt then return false, _; end if;
   W := Parent (w);
   if not assigned G`SLPGroup then 
      G`SLPGroup := W; 
      G`SLPGroupHom := hom <W -> G | UserGenerators (G)>;
   end if;
   if not (TensorProductFlag (G) cmpeq true) then 
      if IsScalar (g * G`SLPGroupHom (w)^-1) eq false then 
         return false, _; 
      end if;
   end if;
   return w;
end function;

intrinsic SL2ElementToWord (G:: GrpMat, g:: Mtrx) -> GrpSLPElt
{if g is element of G which has been constructively recognised to have
 central quotient isomorphic to PSL(2, q), then return element of 
 word group of G which evaluates to g, else false}

   w := MySL2ElementToWord (G, g);
   if Type (w) eq GrpSLPElt then 
      return true, w;
   else
      return false, _;
   end if;
end intrinsic;
