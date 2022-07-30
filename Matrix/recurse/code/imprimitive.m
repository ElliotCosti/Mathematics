ImageOfImprimitiveElement := function (G, g)
   return ImprimitiveAction (G, g);
end function;

ImprimitiveImage := function (G)
   B := Blocks (G);
   n := #B;
   images := [ImageOfImprimitiveElement (G, g): 
               g in UserGenerators (G)];
   I := sub <Sym (n) | images>;
   I`UserGenerators := [I.j: j in [1..Ngens (I)]];
   return I, true;
end function;

ElementsActImprimitively := function (G, TestElements)
   B := Blocks (G);
   n := #B;
   for g in TestElements do 
      list := {Position (B, B[i]^g): i in [1..#B]};
      if Set (list) ne {1..n} then return false; end if;
   end for;
   return true;
end function;
