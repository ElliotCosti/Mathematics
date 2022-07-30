/* version of centraliser of involution without storing words */

BrayGenerators := function (P, g: fct := Order)
   repeat
      h := Random (P);
   until h^2 ne h^0;
   c := (g, h);
   o := fct (c);
   m := o div 2;
   if IsEven (o) then
      return [c^m, (g, h^-1)^m], h;
   else
      return [h * c^m], h;
   end if;
end function;                          

OddBrayGenerators := function (P, g: fct := Order, Limit := 50)
   nmr := 0;
   repeat 
      nmr +:= 1;
      repeat 
         h := Random (P);
      until h^2 ne h^0;
      c := (g, h);
      o := fct (c);
      m := o div 2;
      if IsOdd (o) then 
         return true, [h * c^m], h;
      end if;
   until nmr eq Limit;
   return false, _;
end function;

/* centraliser of involution g in G; do not store words */

BrayCentraliser := function (G, g: fct := Order, N := 5)

   d := Degree (G);
   if Type (G) eq GrpMat then
      F := BaseRing (G);
      L := GL(d, F);
   elif Type (G) eq GrpPerm then 
      L := Sym (d);
   else 
      L := G;
   end if;

   E := [[g]]; 
   P := RandomProcess (G);

   for i in [2..N + 2] do
      flag, E[i] := OddBrayGenerators (P, g: fct := fct);
      if not flag then 
         "No odd Bray generators found";
         E[i] := BrayGenerators (P, g: fct := fct);
      end if;
   end for;
   // "Lengths are ", [#e: e in E];
   E := &cat(E);

   return sub <L | E>;

end function;
