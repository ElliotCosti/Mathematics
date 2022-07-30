PowerMap := function (G, g)
   C := CentralisingMatrix (G);
   e := DegreeOfFieldExtension (G);
   d := Degree (G);
   F := BaseRing (G);
   q := #F;
   V := VectorSpace (F, d);
   v := V.1; // v is the vector (1, 0, 0, 0, ...)
   L := v * C * g;
   M := v * g;
   N := C;
   i := 0;
   repeat
      R := M * N;
      if L eq R then
         return i;
      else
         N := N^q; i +:= 1;
      end if;
   until i eq e;
   return false;
end function;

CyclicGroupNode := function (G)
   U := UserGenerators (G);
   e := DegreeOfFieldExtension (G);
   image := [PowerMap (G, U[i]): i in [1..#U]];
   E := CyclicGroup (e);
   images := [E.1^image[i]: i in [1..#U]];
   k, a := XGCD (image cat [e]);
   gen := E.1^k;
   G`Basis := gen;
   E := sub <E | images>;
   E`UserGenerators := images;
   return E;
end function;

ImageOfSemilinearElement := function (G, g)
   k := G`Basis;
   power := PowerMap (G, g); 
   if (power cmpeq false) then 
      error "Element does not act semilinearly";
   end if; 
   return k^power;
end function;

ElementsActSemilinearly := function (G, TestElements) 
   for g in TestElements do 
      power := PowerMap (G, g); 
      if (power cmpeq false) then 
         return false;
      end if; 
   end for;
   return true;
end function;
