ImageOfTensorElement := function (G, g)
   F := BaseRing (G);
   CB := TensorBasis (G);
   u, w := TensorDimensions (G);
   flag, facs := IsProportional (g^CB, u);
   if flag then return GL(w, F) ! facs[2]; end if;
   error "Element does not have a tensor decomposition";
end function;

/* image of scalar is generator for GF(q)^* */

ImageOfTensorScalar := function (G, alpha)
   F := BaseRing (G);
   CB := TensorBasis (G);
   u, w := TensorDimensions (G);
   omega := PrimitiveElement (F);
   return GL(w, F) ! ScalarMatrix (w, omega);
end function;

TensorImage := function (G)
   F := BaseRing (G);
   CB := TensorBasis (G);
   u, w := TensorDimensions (G);

   images := [g^CB : g in UserGenerators (G)];
   flag, fac := AreProportional (images, u);

   /* image of scalar is generator for GF(q)^* */
   fac := [ImageOfTensorScalar (G, images[1])] 
          cat [fac[i][2] : i in [2..#fac]];
   fac := [GL(w, F) ! f : f in fac];
   I := sub <GL(w, F) | fac>;
   I`UserGenerators := fac;
   return I, true;
end function;

ElementsActAsTensor := function (G, TestElements)
   CB := TensorBasis (G);
   u, w := TensorDimensions (G);
   return AreProportional ([g^CB: g in TestElements], u);
end function;                     
