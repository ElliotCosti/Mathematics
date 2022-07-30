/* alpha is a scalar matrix */

ImageOfScalar := function (G, alpha)

   if not assigned G`ActionType then
      error "ImageOfScalar: Problem in ActionType";
   end if;

   if G`ActionType eq "reducible" then
      return ImageOfReducibleElement (G, alpha);
   elif G`ActionType eq "unipotent" then
      return ImageOfUnipotentElement (G, alpha);
   elif G`ActionType eq "imprimitive" then
      return ImageOfImprimitiveElement (G, alpha);
   elif G`ActionType eq "absolutereducible" then
      return ImageOfAbsolutelyReducibleElement (G, alpha);
   elif G`ActionType eq "semilinear" then
      return ImageOfSemilinearElement (G, alpha);
   elif G`ActionType eq "tensor" then
      return ImageOfTensorScalar (G, alpha);            
   elif G`ActionType eq "tensorinduced" then
      return ImageOfTensorInducedElement (G, alpha);            
   elif G`ActionType eq "smaller" then
      return ImageOfSmallerFieldScalar (G, alpha);            
   elif G`ActionType eq "extra" then
      return ImageOfExtraSpecialElement (G, alpha);            
   elif G`ActionType eq "determinant" then
      return ImageOfDeterminantScalar (G, alpha);            
   else
      error "ElementsSatisfyAschbacher: Problem in ActionType";
   end if;

end function;                     

/* alpha is a scalar matrix */

InitialiseKernel := function (G, alpha)

   if not assigned G`ActionType then
      error "InitialiseKernel: Problem in ActionType";
   end if;

   S := G`SLPGroup;

   d := Degree (G); F := BaseRing (G);
   if G`ActionType eq "reducible" then
      return [ GL (d, F) ! Identity (G)], [Identity (S)];
   else 
      return [ GL (d, F) ! alpha], [S.1];
   end if;

end function;                     
