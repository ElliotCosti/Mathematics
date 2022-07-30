RandomConjugate := function (G)
   P := GL (Degree (G), BaseRing (G));
   x := Random (P);
   return sub < P | [G.i^x : i in [1..Ngens (G)]]>, x;
end function;
                        
/* construct standard example */

ConstructExample := function (d, q, n)

   G := GL(d, q);
   S := Sym (n);
   G := TensorWreathProduct (G, S);
   ran := Random (GL(d^n, q));
   G := sub < GL(d^n, q) | {g^ran : g in Generators (G)}>;
   return G;

end function;

TensorProd := function (U)
 
   a := U[1];
   for i in [2..#U] do
      a := TensorProduct (a, U[i]);
   end for;
   return a;
 
end function;     

/* construct G wr S */

ConstructGroup := function (G, S)

   n := Degree (S);
   d := Degree (G);
   F := BaseRing (G);
   G := TensorWreathProduct (G, S);
   ran := Random (GL(d^n, F));
   G := sub < GL(d^n, F) | {g^ran : g in Generators (G)}>;
   return G;
end function;

WriteOverLarge := function (G, e: Scalars := false)

   F := BaseRing (G);
   d := Degree (G);
   E := ext < F | e >;

   r := Random (GL(d, E)); rm1 := r^-1;
   H := sub < GL(d, E) | [G.i: i in [1..Ngens (G)]]>;
   H := sub < GL(d, E) | [rm1 * H.i * r: i in [1..Ngens (G)]]>;
   if Scalars then 
      w := PrimitiveElement (E);
      H := sub < GL(d, E) | H, rm1 * ScalarMatrix (d, w) * r>;
   end if;
   return H;

end function;
