InvolutionSp4 := function (G)
   X := ConstructEven (G);
   X := Rep (X);
   g := X[1];
   w := X[2];
   o := Order (g);
   g := g^(o div 2);
   w := w^(o div 2);
   W1 := Parent (w);
   if assigned G`SLPGroup then 
      W := G`SLPGroup;
      tau := hom < W1 -> W  | [W.i: i in [2..Ngens (W)]]>;
      w := tau (w);
   end if;
   return g, w;
end function;
