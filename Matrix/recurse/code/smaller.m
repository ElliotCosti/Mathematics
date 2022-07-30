ImageOfSmallerFieldElement := SmallerFieldImage; 

/* image of scalar is generator for GF(q)^* */
ImageOfSmallerFieldScalar := function (G, alpha)
   F := SmallerField (G);
   d := Degree (G);
   w := PrimitiveElement (F);
   return GL(d, F) ! ScalarMatrix (d, w);
end function;              

ElementsOverSmallerField := function (G, TestElements) 
   F := SmallerField (G); d := Degree (G);
   gl := GL (d, F);
   for g in TestElements do
      im := ImageOfSmallerFieldElement (G, g);
      if Type (im) eq BoolElt then return false; end if;
      P := Parent (im);
      if BaseRing (P) ne F then 
         return false;
      end if;
   end for;                    
   return true;
end function;

GroupSmallerFieldImage := function (G)
   U := UserGenerators (G);
   F := SmallerField (G); 
   d := Degree (G);
   /* image of scalar is generator for GF(q)^* */
   gens := [ImageOfSmallerFieldScalar (G, U[1])] cat 
             [ImageOfSmallerFieldElement (G, U[i]) : i in [2..#U]];
   I := sub <GL(d, F) | gens>;
   I`UserGenerators := gens;
   return I, true;
end function;
