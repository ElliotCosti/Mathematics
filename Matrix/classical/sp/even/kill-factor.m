/* kill factors specified by Blist, ensuring that there
   is required action on all of the the factors specified by Alist;
   each list is a sequence of index positions; 

   if Squares are true, then squares of generators must 
   also generate requisite action [required in AB formula];
   
   if words are true, then we record generators for desired
   subgroup as words in user-generators of P, the parent of G */

KillFactor := function (P, G, Alist, Blist: Squares := false, 
                       Parent := true, Words := false, Limit := 100) 

   d := Degree (G);
   F := BaseRing (G);

   while [] in Alist do Exclude (~Alist, []); end while;
   while [] in Blist do Exclude (~Blist, []); end while;
  
   nmr := 0;
   repeat 
      if Words then 
         g, wg := RandomWord (G);
      else 
         g := Random (G);
      end if;
      nmr +:= 1;
      B := [* ExtractAction (g, Blist[i]): i in [1..#Blist] *];
      OB := [Order (x): x in B]; 
      o := LCM (OB);
      A := [* ExtractAction (g, Alist[i]): i in [1..#Alist] *];
      /* avoid generating sets composed of involutions */
      required := forall{i : i in [1..#A] | not IsScalar (A[i]^(2 * o))};
   until required or nmr gt Limit * 10;

   if nmr gt Limit then 
      G:Magma;
      error "Failed to construct non-trivial action", Alist, Blist;
   end if;

   vprint User5:
   "Nmr checked to find non-trivial action = ", nmr;

   vprint User5:
   "Chosen generator now has projective order ", ProjectiveOrder (g); 

   g := g^(o);
   Large := [g^0, g];
   if Words then wg := wg^(o); WA := [wg^0, wg];end if;

   /* is the group SL on required factors and trivial on remaining ones */
   IsGoodGroup := function (H, required) 
      S := Sections (H);
      degs := [Degree(s): s in S];
      nontrivial := [x : x in degs | x ne 1];
      Sort (~nontrivial);
      return (nontrivial eq required and 
              forall{x : x in S | RecognizeClassical (x)});
   end function;

   required := [#x : x in Alist];
   Sort (~required);
   Nmr := 0;
   repeat 
      Nmr +:= 1;
      if Words then 
         k, wk := RandomWord (G);
      else 
         k := Random (G);
      end if;
      Append (~Large, g^k);
      if Words then Append (~WA, wg^wk); end if;
      H := sub <GL(d, F) | Large>;
      flag := IsGoodGroup (H, required); 
      if Squares then 
         K := sub <GL(d, F) | [x^2 :x in Large]>;
         flag := IsGoodGroup (K, required); 
      end if;
   until flag or Nmr gt Limit;
    
   if Nmr gt Limit then 
      error "Failed to construct desired action", Alist, Blist;
   end if;
   vprint User5: "Nmr of conjugates needed to generate action is ", #Large - 2;

   if Words then 
      OrigWA := WA;
      if Parent then 
         theta := hom <G`SLPGroup -> P`SLPGroup | G`UserWords>;
         WA := [theta (w): w in WA];
      end if;
      H`UserWords := WA;
      H`UserGenerators := Large;
      H`SLPGroup := SLPGroup (#Large);
      H`SLPGroupHom := MyHom (H, H`SLPGroup, H`UserGenerators);
      return H, true, OrigWA;
   end if;

   return H, true;
end function;
