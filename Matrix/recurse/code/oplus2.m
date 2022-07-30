FormOmegaPlus2 := function (G: Proper := true, Exact := false)
     F := BaseRing (G);
     if #F le 5 then 
        return true, MatrixAlgebra (F, 2) ![ 0, 1, 1, 0];
     end if;
     M := GModule (G);
     N := Dual (M);
     mat := KMatrixSpace (BaseRing (G), 2, 2);
     Ghom := sub < mat | Basis (AHom (M, N)) >;
/*
     if Dimension (Ghom) lt 2 then
         // this would occur, for instance, if <G> = GOPlus
         return false;
     end if;
*/
     sym := sub < mat | [ [1,0,0,0], [0,1,1,0], [0,0,0,1] ] >; 
     Gsym := Ghom meet sym;
     if Dimension (Gsym) ne 1 then
         // <G> does not preserve a unique symmetric form
         return false, _;
     else
         form := MatrixAlgebra (BaseRing (G), 2)!Gsym.1;
         pol := Polynomial ([ form[1][1], 2*form[1][2], form[2][2] ]);
         if #Roots (pol) eq 0 then
	    return false, _;
         end if;
         return true, form;
     end if;
     return false, _;
end function;

// given a 2x2 matrix group <G> over finite field <F>
// of odd characteristic, this function decides if
// it contains Omega^+ (2, <F>)
// if SpecialGroup then it decides if G is SO+(2, F)

ContainsOmegaPlus2  := function (G: SampleSize := 20, SpecialGroup := false);

    F := BaseRing (G);
    q := #F;
    if q in [3, 5] then
       if IsTrivial (G) then return false, _; end if;
       o := #G;
       if  SpecialGroup then return o gt (q - 1) div 2, _; end if;
       return o ge (q - 1) div 2;
   end if;

    flag, form := FormOmegaPlus2 (G);
    if flag eq false then return false, _; end if;

    required := (q - 1)  div Gcd (2, q - 1);
    x := ElementOfOrder (G, required, SampleSize: Word:=false);
    if x cmpeq false then return false, _; end if;

    if SpecialGroup then 
       // now <form> has type +
       // check gens of <G> have correct spinor norm
       return exists {i : i in [1..Ngens (G)] | 
                          SpinorNorm (G.i, form) eq 1}, x;
    end if;

    return true, x;
end function;
