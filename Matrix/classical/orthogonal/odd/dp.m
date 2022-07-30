DPActionElement := function (G, P, action, list, form: Limit := 50,
                             Scalar := false, Words := true, 
                             Partial := false, SpecialGroup := false)
t := Cputime ();

   nmr := 0;
   repeat 
      nmr +:= 1;
      if Words then 
         g, wg := RandomWord (G);
      else 
         g := Random (P);
      end if;
      a := ExtractAction (g, action);
      b := ExtractAction (g, list);
      a, power := ObtainActionOnFactor (G, g, a, b); 
      if Scalar eq true then 
         required := not IsScalar (a);
      else 
         required := not IsIdentity (a);
      end if;
      if required and (Partial or SpecialGroup) then
         if #action eq 2 and IsIdentity (form) then 
            required := IsEven (Order (a));
         else 
            value := SpinorNorm (a, form);
            required := value eq 1;
         end if;
      end if;
   until required eq true or nmr gt Limit;

"nmr is ", nmr;
"Time to A is ", Cputime (t);

   if nmr gt Limit then return false, _, _, _; end if;

   g := g^(power);
   if Words then
      wg := wg^(power); 
      return true, g, a, wg;
   else 
      return true, g, a, _;
   end if;
end function;

TypeOfGroup := function (type)
   case type:
      when "linear": f := MyIsLinearGroup;
      when "symplectic": f := MyIsSymplecticGroup;
      when "unitary": f := MyIsUnitaryGroup;
      when "orthogonalplus": f := MyIsSOPlusGroup;
      when "orthogonalminus": f := MyIsSOMinusGroup;
      when "orthogonalcircle": f := MyIsSOGroup;
      else f := func <G | Type (G) eq GrpMat>;
   end case;
   return f;
end function;

MyOrthogonalForm := function (G)
   if Degree (G) eq 2 then
      flag, quad, form, type := OrthogonalForm2 (G);
   else 
      flag, form, type := SymmetricBilinearForm (G);
   end if;
   if flag then return true, form; end if;
   return false, _; 
end function;

MyOrthogonalForm  := OrthogonalForm;

MyLinearForm := function (G)
   flag := ClassicalForms (G)`formType eq "linear";
   if flag eq true then return flag, Identity (G); else return flag, _; end if;
end function;

TypeOfForm := function (G, type)
   case type:
      when "linear": f := MyLinearForm;
      when "symplectic": f := SymplecticForm;
      when "unitary": f := UnitaryForm;
      when "plus", "orthogonalplus": f := OrthogonalForm; 
      when "minus", "orthogonalminus": f := OrthogonalForm;
      when "circle", "orthogonalcircle": f := OrthogonalForm; 
   end case;
   return f;
end function;

/* store generators for H as words in P */
procedure StoreWords (P, G, H, WA)
   theta := hom <G`SLPGroup -> P`SLPGroup | G`UserWords>;
   WA := [theta (w): w in WA];
   H`UserWords := WA;
   H`SLPGroup := SLPGroup (#WA);
   H`SLPGroupHom := MyHom (H, H`SLPGroup, H`UserGenerators);
end procedure;

/* kill factor specified by list; construct subgroup of G which has 
   classical action on factors of dimension listed in f; 
   P is parent of G, words are rewritten as words in P  */

SOGoodCentraliser := function (P, G, desired, list: 
   type := "orthogonalplus", fct := Order,
   Scalar := false, Partial := false, SpecialGroup:= false, 
   Words := true, Limit := 20) 

   if #list eq 0 then return G; end if;

   if Type (desired) eq SetEnum then
      desired := SetToSequence (desired);
   end if;

   if Type (desired) eq SeqEnum then 
      Sort (~desired); f := &+desired; 
   else 
      f := desired; desired := [f]; 
   end if;

   d := Degree (G);
   F := BaseRing (G);
   q := #F;
   action := {1..d} diff list;
   action := Sort (SetToSequence (action));
   assert #action eq f;

   if not Words then P := RandomProcess (G); end if;

   A := [];
   WA := [];
   Large := [];

   H := ExtractFactor (G, action);

   Large := [Identity (G)];
   A := [Identity (GL(Degree (H), q))];
   if Words then WA := [Identity (G`SLPGroup)]; end if;
   
   if IsTrivial (H) then 
      H := sub < GL(d, F) | Large>;
      H`UserGenerators := Large;
      if Words then StoreWords (P, G, H, WA); end if;
      return H;
   else 
      type_fn := TypeOfForm (H, type);
      flag, form := type_fn (H);
   end if;

   group_fn := TypeOfGroup (type);

   if (Degree (H) eq 2) then Nmr := 50; 
   elif type eq "orthogonalplus" and Degree (H) le 4 then Nmr := 40; 
   else Nmr := 5; end if;

t := Cputime ();
   for i in [1..Nmr] do
      flag, g, a, wg := DPActionElement (G, P, action, list, form: Words := Words);
      if flag and Position (Large, g) eq 0 then 
         Large cat:= [g];
         A cat:= [a];
         if Words then WA cat:= [wg];end if;
      end if;
   end for;
"time to a is ", Cputime (t);

t := Cputime ();
   found := false;
   nmr := 0;
   if Partial or SpecialGroup then 
      repeat 
         nmr +:= 1;
         flag, g, a, wg := DPActionElement (G, P, action, list, form: 
            Partial := Partial, Words := Words, SpecialGroup := SpecialGroup);
         if flag then
            if Position (Large, g) eq 0 then 
               Large cat:= [g];
               A cat:= [a];
               if Words then WA cat:= [wg];end if;
            end if;
         end if;
      until nmr gt Limit or flag;
   end if;
"time to b is ", Cputime (t);

t := Cputime ();
   nmr := 0; r := #A;
   repeat 
      nmr +:= 1;
      if Words then 
         k, wk := RandomWord (G);
      else 
         k := Random (P);
      end if;
      for j in [2..#A] do
         g := Large[j];
         a := A[j];
         h := g^k; 
         if Position (Large, h) eq 0 then 
            Append (~Large, g^k);
            ak := ExtractAction (k, action);
            Append (~A, ak^-1 * a * ak);
            if Words then wg := WA[j]; Append (~WA, wg^wk); end if;
         end if;
      end for;
      H := sub <GL(f, F) | A>;
      found := group_fn (H);
   until found or nmr gt Limit;
"time to c is ", Cputime (t);
 
   if nmr gt Limit then 
      "Special = ", SpecialGroup;
      "Partial = ", Partial;
      "type = ", type;
       G:Magma; "desired is ", desired; "kill =", list;
      "found so far", H:Magma;
      error "Failed to construct factors"; 
   end if;
   vprint User5: "Number of conjugates needed to construct factors is ", #A - 2;

   H := sub <GL(d, F) | Large>;
   H`UserGenerators := Large;
   if Words then StoreWords (P, G, H, WA); end if;
   return H;
end function;
