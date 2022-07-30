CentralisingSpace := function (b)
   P := Parent (b);
   F := BaseRing (P);
   d := Degree (P);
   MA := MatrixAlgebra (F, d);
   x := MA!b - Identity (MA);
   return (Nullspace (x));
end function;

/* y is (projective) involution; 
   does its centraliser suitably split space? */
 
IsGoodInvolution := function (H, y, range)

   S := CentralisingSpace (y);
   s := Dimension (S);
   d := Degree (H);
   if s in range or (d - s) in range then return true, s; end if;

   /* possible projective order 2 */
   if y^2 ne y^0 then 
      F := BaseRing (H);
      flag, w := IsSquare (F!-1);
      if flag then 
         y1 := ScalarMatrix (d, w) * y;
         S := CentralisingSpace (y1);
         s := Dimension (S);
         "second s is  now ", s;
         return s in range or (d - s) in range, s; 
      else
         return true, d div 2;
      end if;
   else
      return false, s;
   end if;
end function;

/* first and second involutions */

ChooseInvolution := function (H, g : LIMIT := 100, fct := Order)

   d := Degree (H);

   if Characteristic (BaseRing (H)) eq 2 then
      range := [d div 2.. d div 2 + 2];
   else 
      range := [d div 2..5 * d div 8]; 
   end if;
   if #range eq 0 then error "range is too narrow"; end if; 
   if d eq 4 then range := [2]; end if;

   nmr := 0;
   I := []; E := []; W := []; Dim := [];
   repeat
     nmr +:= 1;
     h, wh := RandomWord (H);
     gh := g * h;
     o := fct (gh);
     if IsEven (o) then 
        z := (gh)^(o div 2);
        if IsScalar (z) eq false then 
           flag, s := IsGoodInvolution (H, z, range);
           if flag then 
              vprint User1: "Number of elements sampled to find suitable involutions is ", nmr;
              return z, h, wh, s;
           end if;
           I[#I + 1] := z;
           E[#E + 1] := h;
           W[#W + 1] := wh;
           Dim[#Dim + 1] := s;
        end if;
     end if;
   until nmr gt LIMIT;

   mid := d div 2;
   X := [AbsoluteValue (x - mid) : x in Dim];
   if #X eq 0 then return $$ (H, g); end if;
   min, pos := Minimum (X);

   return I[pos], E[pos], W[pos], Dim[pos];

end function;

ThirdInvolution := function (H, z, t: LIMIT := 100, fct := Order)

   d := Degree (H);
   F := BaseRing (H);

   if Characteristic (BaseRing (H)) eq 2 then
      range := [d div 2.. d div 2 + 2];
   else 
      range := [d div 2 - 1..5 * d div 8 + 1]; 
   end if;
   if #range eq 0 then error "range is too narrow"; end if; 

   I := []; E := []; W := []; Dim := [];
   nmr := 0;
   repeat 
      nmr +:= 1;
      a, wa := RandomWord (H);
      y := z^a * t;
      o := fct (y);
      if IsEven (o) then 
         y := y^(o div 2);
         if IsScalar (y) eq false then 
            flag, s := IsGoodInvolution (H, y, range);
            if flag then 
               return y, a, wa, s;
            end if;
            I[#I + 1] := y;
            E[#E + 1] := a;
            W[#W + 1] := wa;
            Dim[#Dim + 1] := s;
         end if;
      end if;
   until nmr gt LIMIT;

   if nmr gt LIMIT then 
      error "Failed to construct third non-scalar involution"; 
   end if;

   mid := d div 2;
   X := [AbsoluteValue (x - mid) : x in Dim];
   if #X eq 0 then return $$ (H, z, t); end if;
   min, pos := Minimum (X);

   return I[pos], E[pos], W[pos], Dim[pos];

end function;

/* implementation of Ryba strategy for membership testing;
   given H subgroup of G, decide if g an element of G is
   also element of H  */

ClassicalRyba := function (H, g : Verify := false, LIMIT := 100, 
                                  Direct := false, fct := Order)
// "Entry to CLASSICAL RYBA";
   if Direct then 
      _ := InitialiseGroup (H);
   end if; 

   if IsIdentity (g) or Ngens (H) eq 0 then 
      return true, Identity (H`SLPGroup);
   end if;

   vprint User1: "order of g is ", Order (g);

   /* find h such that g * h has even order to obtain involution z */
   z, h, wh, fixed := ChooseInvolution (H, g: fct := fct);
   vprint User1: "Fixed z is ", fixed;
   gh := g * h;

   /* find t an H-involution, distinct from z */
   nmr := 0; L := LIMIT div 10; d := Degree (H);
   repeat 
      t, one, two, fixed := ChooseInvolution (H, Id (H): fct := fct); 
      o := fct (one);
      wt := two^(o div 2);
      vprint User1: "Fixed t is ", fixed;
      nmr +:= 1;
      complete := (t cmpeq false) or (z ne t) or (nmr eq L);
   until complete;
   
   if t cmpeq false or z eq t then 
      "part II: order of g is ", Order (g);
      return AlternativeSolution (H, g); 
   end if;

   /* find a random H-conjugate of z such that z * t has 
      even order and so obtain a third involution y */
  
   y, a, wa, fixed := ThirdInvolution (H, z, t: fct := fct);
   z := z^a; 
/* 
   if nmr gt LIMIT then 
      "part III: order of g is ", Order (g);
      return AlternativeSolution (H, g); 
   end if;
*/

   vprint User1: "Fixed y is ", Dimension (CentralisingSpace (y));

   /* construct centraliser T of t in H and decide
      if y is in T */
   vprint User1: "First Centraliser";
   T, x, wx := ConstructCentraliser (H, t, wt : KernelRank := 20, fct := fct);

   if Verify then 
      "order of t-centraliser is ", #T[1]`group;
       assert #T[1]`group eq #Centraliser (H, t); 
   end if;

   flag, wy := WriteElement (H, T, y, x, wx);
   if not flag then return false, _; end if;

   /* construct centraliser Y of y in H and decide
      if z is in Y */
   vprint User1: "Second Centraliser";
   Y, x, wx := ConstructCentraliser (H, y, wy : KernelRank := 20, fct := fct);

   if Verify then 
      "order of y-centraliser is ", #Y[1]`group;
       assert #Y[1]`group eq #Centraliser (H, y); 
   end if;

   flag, wz := WriteElement (H, Y, z, x, wx);
   if not flag then return false, _; end if;

   /* construct centraliser Z of z in H and decide
      if g * h is in Z */
   vprint User1: "Third Centraliser";
   Z, x, wx := ConstructCentraliser (H, z, wz : KernelRank := 20, fct := fct);

   if Verify then 
      "order of z-centraliser is ", #Z[1]`group;
       assert #Z[1]`group eq #Centraliser (H, z); 
   end if;

   gh := gh^a;
   flag, wgh := WriteElement (H, Z, gh, x, wx);
   if not flag then return false, _; end if;

   delta := H`SLPGroupHom;
   wg := wa * wgh * wa^-1 * wh^-1;
   assert IsScalar (delta (wg) * g^-1);
   vprint User1:"Here we are at end of Ryba";

   return true, wg;

end function; 
