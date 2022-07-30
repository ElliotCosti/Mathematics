AbsoluteReducibleImage := function (G)
   U := UserGenerators (G);
   flag := IsAbsolutelyIrreducible (G);
   assert flag eq false;
   I, phi := AbsoluteRepresentation (G);
   G`AbsoluteMap := phi;
   k := Degree (Image (phi));
   K := BaseRing (Image (phi));
   I`UserGenerators := [GL(k, K) ! phi (u): u in U];
   return I;
end function;

ImageOfAbsolutelyReducibleElement := function (G, g)
   phi := G`AbsoluteMap;
   k := Degree (Image (phi));
   K := BaseRing (Image (phi));
   return GL(k, K) ! phi (g);
end function;

ElementsActAbsolutelyReducibly := function (G, TestElements) 
   for g in TestElements do 
      image := ImageOfAbsolutelyReducibleElement (G, g);
      if (image cmpeq false) then 
         return false;
      end if; 
   end for;
   return true;
end function;
