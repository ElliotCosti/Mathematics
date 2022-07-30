/* construct projection of h in G to section of G described by S; 
   S may be composition factor or one which has further decomposed
   into tensor factor */

ProjectionOfElement := function (G, S, h)
   F := BaseRing (G);
   index := S[2];
   blocks := MatrixBlocks (G, h);
   image := blocks[index];
   if S[4] eq 0 then
      return blocks[index];
   elif S[4] ne 0 then 
      CB := TensorBasis (S[1]);
      dim := TensorDimensions (S[1]);
      image := image^CB; 
      flag, factors := IsProportional (image, dim);
      if not flag then error "not a tensor product"; end if;
      m := Nrows (factors[S[4]]);
      return GL(m, F) ! factors[S[4]];
   end if;
   return false;
end function;
   
ProjectiveBrayGeneratorsWords := function (G, S, g, wg: Limit := 50)
   repeat 
      h, wh := RandomWord (G);
      hi := ProjectionOfElement (G, S, h);
   until hi^2 ne hi^0;
   c := (g, h);
   ci := ProjectionOfElement (G, S, c);
   o := ProjectiveOrder (ci);
   m := o div 2;
   if IsEven (o) then 
      return [c^m, (g, h^-1)^m], 
             [(wg, wh)^m, (wg, wh^-1)^m]; 
   else 
      return [h * c^m], [wh * (wg, wh)^m];
   end if;
end function;

/* find odd order generators if possible */

ProjectiveOddBrayGeneratorsWords := function (G, S, g, wg: Limit := 50)
   nmr := 0;
   repeat 
      nmr +:= 1;
      repeat 
         h, wh := RandomWord (G);
         hi := ProjectionOfElement (G, S, h);
      until hi^2 ne hi^0;
      c := (g, h);
      ci := ProjectionOfElement (G, S, c);
      o := ProjectiveOrder (ci);
      m := o div 2;
      if IsOdd (o) then 
         return true, [h * c^m], [wh * (wg, wh)^m];
      end if;
   until nmr eq Limit;
   return false, _, _;
end function;

/* g involution in G; wg is corresponding word; 
   construct its centraliser */

ProjectiveCentraliserOfInvolution := function (G, SG, g, wg: N := 5, Nmr := 50)

   S := G`SLPGroup;
   F := BaseRing (G);
   d := Degree (G);
   lambda := UserGenerators (G)[1];
   E := [[lambda], [g]]; W := [[S.1], [wg]];

   for i in [3..N + 2] do
      flag, E[i], W[i] := ProjectiveOddBrayGeneratorsWords (G, SG, g, wg);
      if not flag then 
         vprint User5: "No odd Bray generators found";
         E[i], W[i] := ProjectiveBrayGeneratorsWords (G, SG, g, wg);
      end if;
   end for;
   vprint User5: "Lengths are ", [#e: e in E];
   E := &cat(E);
   assert Position (E, g) eq 2;
   W := &cat(W);

   PG := RandomProcess (G);
   R :=  SetToSequence (Set(&cat[BrayGenerators (PG, g): i in [1..Nmr]]));

   C := sub < GL(d, F) | E>;
   C`UserGenerators := E;
   C`UserWords := W;

   B := SLPGroup (#E);
   C`SLPGroup := B;
   C`SLPGroupHom := MyHom (C, B, E);

   C`RandomElements := R;
   return C;
end function;
