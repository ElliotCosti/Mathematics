ConstructAction := function (G)

   if Ngens (G) eq 0 then return false, G; end if;

   if IsUnipotent (G) then 
      vprint User1: "**** Unipotent ";
      I := UnipotentAction (G);
      G`ActionType := "unipotent";
      return true, I;
   end if;

   if not IsIrreducible (G) then 
      vprint User1: "**** Reducible ";
      flag, I := ReducibleAction (G);   
      G`ActionType := "reducible";
      return true, I;
   end if;

   if CanApplyDiscreteLog (BaseRing (G)) then 
      flag := GroupDeterminants (G);
      if flag then 
         vprint User1: "**** Group has non-trivial determinants";
         I := DeterminantImage (G);
         G`ActionType := "determinant";
         return true, I;
      end if;
   end if;

   if not IsAbsolutelyIrreducible (G) then 
      vprint User1: "**** Absolutely reducible ";
      I := AbsoluteReducibleImage (G);
      G`ActionType := "absolutereducible";
      return true, I;
   end if;

   if IsSemiLinear (G) cmpeq true then
      vprint User1: "**** Semilinear";
      I := CyclicGroupNode (G);      
      G`ActionType := "semilinear";
      return true, I;
   end if;

   if IsPrimitive (G) cmpeq false then 
      vprint User1: "**** Imprimitive ";
      I := ImprimitiveImage (G);
      G`ActionType := "imprimitive";
      return true, I;
   end if;

   /* we are seeking to write G modulo scalars over a smaller field;
      if G has dimension 1, this can be done but the kernel 
      is now G ..., and we iterate producing an infinite loop */

   if Degree (G) gt 1 then 
      flag, I := IsOverSmallerField (G : Scalars := false);
      if not flag then 
         flag := IsOverSmallerField (G : Scalars := true);
         if flag then I := GroupSmallerFieldImage (G); end if;
      end if;
      if flag then 
         vprint User1: "**** Over smaller field mod scalars";
         G`ActionType := "smaller";
         return true, I;
      end if;
   end if;

   if RecognizeGroupAsSLd2(G) then 
      vprint User1: "*** SL2 representation";
      return false, G; 
   end if;

   if IsExtraSpecialNormaliser (G) cmpeq true then
      vprint User1: "**** ExtraSpecialNormaliser";
      I := ExtraSpecialImage (G);      
      G`ActionType := "extra";
      return true, I;
   end if;

   if IsTensor (G) cmpeq true then
      vprint User1: "**** Tensor product";
      I := TensorImage (G);
      G`ActionType := "tensor";
      return true, I;
   end if;

   if IsTensorInduced (G) cmpeq true then 
      vprint User1: "**** Tensor induced ";
      I := TensorInducedImage (G);
      G`ActionType := "tensorinduced";
      return true, I;
   end if;

   return false, G;

end function;

ConstructImage := function (G, u)

   if not assigned G`ActionType then
      error "in ConstructImage";
   end if;

   if G`ActionType eq "reducible" then 
      return ImageOfReducibleElement (G, u);
   elif G`ActionType eq "unipotent" then
      return ImageOfUnipotentElement (G, u);
   elif G`ActionType eq "imprimitive" then
      return ImageOfImprimitiveElement (G, u);
   elif G`ActionType eq "absolutereducible" then
      return ImageOfAbsolutelyReducibleElement (G, u);
   elif G`ActionType eq "semilinear" then
      return ImageOfSemilinearElement (G, u);
   elif G`ActionType eq "tensor" then
      return ImageOfTensorElement (G, u);
   elif G`ActionType eq "tensorinduced" then
      return ImageOfTensorInducedElement (G, u);
   elif G`ActionType eq "smaller" then
      return ImageOfSmallerFieldElement (G, u);
   elif G`ActionType eq "extra" then
      return ImageOfExtraSpecialElement (G, u);
   elif G`ActionType eq "determinant" then
      return ImageOfDeterminantElement (G, u);
   end if;

end function;

NodeIsLeaf := function (node, flag, I)

   if flag eq false or Ngens (I) eq 0 then
      vprint User1: "Node is designated leaf";
      node`type := "leaf";
      G := GroupOfNode (node);
      if Type (G) eq GrpMat then 
         if IsSL2Group (G) cmpeq true then 
            flag := true;
         elif Degree (G) gt 1 then 
            if IsAbsolutelyIrreducible (G) then 
            flag := RecognizeClassical (G);
            if flag then 
               vprint User1: "Leaf is of type ", ClassicalType (G),
                             "and degree ", Degree (G); 
             end if;
            else flag := false;
            end if;
         else 
            flag := false;
         end if;
         if not (flag cmpeq true) then 
            vprint User1: "Call SimpleGroupName";
            // flag, name := SimpleGroupName (G);
            // if flag and assigned name then 
               // vprint User1: "Leaf contains ", name; 
            // end if;
         end if;
         if assigned G`Submodule then delete G`Submodule; end if;
      end if;
      WordProblemForLeaf (~node);
      node`group := G;
      return true, node;
   else 
      node`type := "nonroot";
      return false, node;
   end if;

end function;
