/* are the last GcdNmrTries entries identical?
   if so, we believe we have found the correct order */

IsGcdSettled := function (L, GcdNmrTries)

   len := #L;
   if L[len] eq 1 then return true; end if;

   if len ge GcdNmrTries then 
      S := {L[len - i + 1] : i in [1..GcdNmrTries]};
      return #S eq 1;
   end if;

   return false;

end function;

/* w is an element of G; approximate its order modulo the normal
   closure in G of subgroup K by repeatedly evaluating the order 
   of w * k, for k an element of the normal closure in G of K, and 
   taking the GCD of resulting orders */

RelativeOrder := function (G, w, K, GcdNmrTries)

   O := []; L := [];

   repeat 
      k := Random (K);
      o := Order (w * k);
      Append (~O, o);
      Append (~L, Gcd (O));
   until IsGcdSettled (L, GcdNmrTries);

   // "Relative order sequence terminates in ", L[#L];
   return L[#L];

end function;

IsNewCoset := function (G, N, O, im)
   return forall{x : x in O | RelativeOrder (G, x * im^-1, N, GcdNmrTries) gt 1};
end function;

ConstructOrbit := function (G, N)

   O := {@ Identity (G) @}; 

   k := 1; DIV := 1;
   /* construct the orbit and stabiliser */
   while k le #O do

      pt := O[k];

      for i in [1..Ngens (G)] do

         /* compute the image of a point */
         im := pt * G.i;

         /* add new element to orbit or stabiliser */
         if IsNewCoset (G, N, O, im) then 
            Include (~O, im);
             if #O mod DIV eq 0 then 
                "Length of orbit is ", #O;  
             end if;
         end if;
      end for;
      
      k +:= 1;

   end while;

   return O;

end function;

IdentifyCoset := function (G, N, O, im)
   flag := exists (k) {k : k  in [1..#O] | RelativeOrder (G, O[k] * im^-1, 
                                                 N, GcdNmrTries) eq 1};
   if flag then return k; else error "in constructing image"; end if;
end function;

ImageOfElement := function (G, N, g, O)
   n := #O;
   S := Sym (n);
   image := [IdentifyCoset (G, N, O, O[i] * g): i in [1..n]];
   if #Set (image) ne n then error "in constructing permutation"; end if;
   return S!image;
end function;
