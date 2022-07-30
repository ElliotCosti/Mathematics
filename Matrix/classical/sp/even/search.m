IsGoodInv := function (G, g)
   B := ClassicalForms (G);
   B := B`bilinearForm;
   F := BaseRing (G);
   d := Degree (G);
   V := VectorSpace (F, d);
   return forall{i : i in [1..d] | MyInnerProduct (B, V.i, V.i^g) eq 0};
end function;

BaseInvolution := function (G)
   nmr := 0;
   repeat 
      g := ElementOfOrder (G, 2, 2000: Word:=false);
      r := Corank (g); 
"rank is ", r;
      nmr +:= 1;
   until r eq 2 and IsGoodInv (G, g);
   return g, nmr;
end function;


