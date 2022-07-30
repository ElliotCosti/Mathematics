/*
input: <G>
output:
   <flag> = true if <G> preserves a quadratic form and contains <Omega>
   <type> = "orthogonalplus" or "orthogonalminus"
   <proper> = true if <G> contains <Omega> as proper subgroup 
   <q_form> = the quadratic form preserved
   <b_form> = the bilinear form preserved
*/

RecognizeOmega2 := function (G : NumberOfElements := 20);

    if IsTrivial (G) then return false, _, _, _, _; end if;

    F := BaseRing (G);
    q := #F;
    MA := MatrixAlgebra (F, 2);

    if q eq 5 then
       o := #G;
       if o eq 2 then  // <Omega> is the only exceptional case
          return true, "orthogonalplus", false, MA![0,1,-1,0], MA![0,1,-1,0];
       end if;
    end if; 

    // q = 4  ... no problems

    if q eq 3 then
       o := #G;
       if o eq 4 then
          if IsCyclic (G) then  // <G> = SOMinus (2, 3)
              return true, "orthogonalminus", true, 
                           MA![0,1,-1,0], MA![0,1,-1,0];
          else // <G> = GOPlus (2, 3)
              return true, "orthogonalplus", true, _, _;
          end if;
       end if;
       if o eq 2 then
          if forall { g : g in G | IsScalar (g) } then  
              return true, "orthogonalminus", false, _, _;
              // this group is also SOPlus (2, 3)
          else
             return false, _, _, _;
          end if;
       end if;
    end if;

    if q eq 2 then
       o := #G;
       if o eq 2 then  // only nontrivial problem group is GOPlus (2, 2)
          return true, "orthogonalplus", true, _, _;
       end if;
    end if;

    // general case

    flag, form, bil, type := OrthogonalForm2 (G);
    if flag eq false then return false, _, _, _, _; end if;

    // now <G> preserves quadratic <form>
    // check that <G> contains Omega
    if type eq 1 then
       required := (q - 1) div Gcd (2, q - 1);
    else 
       required := (q + 1) div Gcd (2, q + 1);
    end if;

    x := ElementOfOrder (G, required, NumberOfElements: Word := false);
    if x cmpeq false then return false, _, _, _, _; end if;

    // check spinor norm
    proper := exists { i : i in [1..Ngens (G)] | SpinorNorm (G.i, bil) eq 1 };

    name := type eq 1 select "orthogonalplus" else "orthogonalminus"; 
    return true, name, proper, form, bil;

end function;

/*
input: <G>
output:
   <flag> = true if <G> preserves a quadratic form and contains <SO>
   <type> = "orthogonalplus" or "orthogonalminus"
   <proper> = true if <G> contains <SO> as proper subgroup 
   <q_form> = the quadratic form preserved
   <b_form> = the bilinear form preserved
*/
RecognizeSO2 := function (G : NumberOfElements := 20);

    if IsTrivial (G) then return false, _, _, _, _; end if;

    F := BaseRing (G);
    q := #F;
    MA := MatrixAlgebra (F, 2);

    // first deal with special cases
    // these are similar to, but easier than, special cases in RecognizeOmega2

    if q eq 2 then
       o := #G;
       if o eq 2 then  // only nontrivial problem group is GOPlus (2, 2)
          return true, "orthogonalplus", false, _, _;
       end if;
    end if;

    if q eq 3 then
       o := #G;
       if o eq 4 then
          if IsCyclic (G) then  // <G> = SOMinus (2, 3)
              return true, "orthogonalminus", false, 
                           MA![0,1,-1,0], MA![0,1,-1,0];
          else // <G> = GOPlus (2, 3)
              return true, "orthogonalplus", true, _, _;
          end if;
       end if;
       if o eq 2 then
          if forall { g : g in G | IsScalar (g) } then  
              return true, "orthogonalplus", false, _, _;
          else
             return false, _, _, _;
          end if;
       end if;
    end if;

    // general case

    if (q mod 2 eq 0) then  // SO = GO, which is nonabelian
 
        if IsAbelian (G) then 
            return false, _, _, _, _; 
        else
            flag, name, proper, form, bil := RecognizeOmega2 (G);
            if flag then
                return true, name, true, form, bil;
            else
                return false, _, _, _, _;
            end if;
        end if;

    end if;

    // if <q> is odd follow a similar path to RecognizeOmega2

    flag, form, bil, type := OrthogonalForm2 (G);
    if flag eq false then return false, _, _, _, _; end if;

    if type eq 1 then
        required := q - 1;
    else 
        required := q + 1;
    end if;

    x := ElementOfOrder (G, required, NumberOfElements: Word := false);
    if x cmpeq false then return false, _, _, _, _; end if;

    // this catches desired cyclic and dihedral groups

    name := type eq 1 select "orthogonalplus" else "orthogonalminus"; 
    return true, name, not IsAbelian (G), form, bil;

end function;
