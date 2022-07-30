ImageOfExtraSpecialElement := function (G, g)
   return ExtraSpecialAction (G, g);
end function;

ExtraSpecialImage := function (G)
   parms := ExtraSpecialParameters (G);
   r := parms[1]; 
   k := parms[2]; k := IsOdd (k) select k - 1 else k - 2;
   images := [ExtraSpecialAction (G, g): g in UserGenerators (G)];
   I := sub <GL(k, r) | images>;
   I`UserGenerators := images;
   return I, true;                       
end function;

ElementsActAsExtraSpecial := function (G, TestElements)
   for g in TestElements do
      image := ExtraSpecialAction (G, g);
      if Type (image) eq BoolElt then return false; end if;
   end for;
   return true;
end function;                
