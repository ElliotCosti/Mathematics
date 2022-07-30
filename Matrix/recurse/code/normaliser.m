ExtField := function ( r, p )

    if not IsPrime(r) or not IsPrime(p) or r eq p then
        "ExtFieldWithRoot: ", r, " and ", p,
                "need to be distinct primes";
    end if;
    e := Order( p, r ); q := p^e;
    return q;
    e := Order( r, p ); q := p^e;
    return q;
    return GF(q);
end function;

PermutationMatrix := function(perm,F)
  //Why is this not an internal function!!!
  //perm permutation, F = field.
  local ps, d, V, W;
  ps := ElementToSequence(perm);
  d := #ps;
  V := RMatrixSpace(F,d,d);
  W := VectorSpace(F,d);
  return V![ W.(ps[i]) : i in [1..d] ];
end function;

PermInducingAut := function(R,phi)
//Given automorphism phi of regular permutation group R, and an automorphism
//phi of R, return unique permutation fixing 1, normalising R and
//inducing phi on R
  local d;
  d := Degree(R);
  perm :=[1];
  for i in [2..d] do
    isc,g := IsConjugate(R,1,i);
    perm[i] := 1^(phi(g));
  end for;
  return Sym(d)!perm;
end function;

NormaliserOfExtraSpecialGroup := function(r,q)
/* Construct complete normaliser of extraspecial group as subgroup of
 * GL(r,q). r must be a prime power p^n with p | q-1.
 * Extraspecial group has order p^(2n+1) and exponent p.
 * (I am dealing with p odd for the moment!)
 */
  local fac, p, n, gl, z, w, esg, d, M, mat, exp, rno, dp, R, phi;
  fac := Factorisation(r);
  if #fac ne 1 then error
     "First argument must be a prime power in NormaliserOfExtraSpecialGroup";
  end if;

  p := fac[1][1]; n := fac[1][2];
  // q := ExtField (r, q);
  q := ExtField (p, q);

  if (q-1) mod p ne 0 then error
     "Divisibility condition not satisfied in NormaliserOfExtraSpecialGroup";
  end if;
  z := PrimitiveElement(GF(q));  w := z^((q-1) div p);
    // w is a primitive p-th root of 1
  gl := GL(r,q);
  // first make generators of extraspecial group
  esg := [gl|];

  //diagonal generators:
  for i in [0..n-1] do
    d := [];
    for j in [1..p^(n-1-i)] do
      for k in [0..p-1] do
        for l in [1..p^i] do Append(~d,w^k); end for;
      end for;
    end for;
    Append(~esg, DiagonalMatrix(GF(q),d));
  end for;

  //for p = 2, q = 1 mod 4, we also take a scalar of order 4
/*
  if p eq 2 and q mod 4 eq 1 then
    Append(~esg, DiagonalMatrix(GF(q),[z^((q-1) div 4): i in [1..r]]));
  end if;
*/

  //permutation matrix generators
  M := func< r,p | r mod p eq 0 select p else r mod p >;
    
  dp := []; // we will collect the permutations for use later.
  for i in [0..n-1] do
    perm := [];
    for j in [1..p^(n-1-i)] do
      for l in [1..p^(i+1)] do
         perm[(j-1)*p^(i+1) + l] := (j-1)*p^(i+1) + M(l+p^i,p^(i+1));
      end for;
    end for;
    Append(~dp,perm);
    Append(~esg, PermutationMatrix(perm,GF(q)) );
  end for;

  //esg now generates extraspecial group of order p^(2n+1).

  //Now normaliser gens.
  esn := [gl|];
  //First diagonals.
  for i in [0..n-1] do
    d := [];
    for j in [1..p^(n-1-i)] do
      exp := 0;
      for k in [0..p-1] do
        exp +:= k;
        for l in [1..p^i] do Append(~d,w^exp); end for;
      end for;
    end for;
    Append(~esn, DiagonalMatrix(GF(q),d));
  end for;

  for i in [0..n-1] do
    mat := MatrixAlgebra(GF(q),p^(i+1))!0;
    rno := 0;
    for j in [1..p^i] do
      for k in [0..p-1] do
         rno +:= 1;
         for l in [0..p-1] do
           mat[rno][j+l*p^i] := w^(k*l);
         end for;
      end for;
    end for;
    mat := DirectSum([mat : j in [1..p^(n-1-i)]]);
    Append(~esn, mat);
  end for;

  //Finally some permutation matrices that normalise it.
  R := sub< Sym(r) | dp >;
  for i in [2..n] do
    phi := hom< R->R | [R.1*R.i] cat [R.j : j in [2..n]] >;
    Append(~esn,PermutationMatrix(PermInducingAut(R,phi),GF(q)));
  end for;

  G := sub< gl | esg cat esn >; H := sub < gl | esg>;
  return G, H;

end function;

NormaliserOfSymplecticGroup := function(r,q)
/* Construct complete normaliser of extraspecial group as subgroup of
 * GL(r,q). r must be a prime power p^n with p | q-1.
 * Extraspecial group has order p^(2n+1) and exponent p.
 * (I am dealing with p odd  for the moment!)
 */
  local fac, p, n, gl, z, w, w4, esg, d, M, mat, exp, rno, dp, R, phi;
  fac := Factorisation(r);
  if #fac ne 1 then error
     "First argument must be a prime power in NormaliserOfSymplecticGroup";
  end if;
  p := fac[1][1]; n := fac[1][2];
  if p ne 2 then error "Prime must be 2 in NormaliserOfSymplecticGroup";
  end if;
  if (q-1) mod 4 ne 0 then error
     "Divisibility condition not satisfied in  NormaliserOfSymplecticGroup";
  end if;
  z := PrimitiveElement(GF(q));  w := z^((q-1) div p);
    // w is a primitive p-th root of 1
  gl := GL(r,q);
  // first make generators of extraspecial group
  esg := [gl|];

  //diagonal generators:
  for i in [0..n-1] do
    d := [];
    for j in [1..p^(n-1-i)] do
      for k in [0..p-1] do
        for l in [1..p^i] do Append(~d,w^k); end for;
      end for;
    end for;
    Append(~esg, DiagonalMatrix(GF(q),d));
  end for;

  //permutation matrix generators
  M := func< r,p | r mod p eq 0 select p else r mod p >;
    
  dp := []; // we will collect the permutations for use later.
  for i in [0..n-1] do
    perm := [];
    for j in [1..p^(n-1-i)] do
      for l in [1..p^(i+1)] do
         perm[(j-1)*p^(i+1) + l] := (j-1)*p^(i+1) + M(l+p^i,p^(i+1));
      end for;
    end for;
    Append(~dp,perm);
    Append(~esg, PermutationMatrix(perm,GF(q)) );
  end for;

  //We also take a scalar of order 4, although this seems to be there anyway!
  w4 := z^((q-1) div 4);
  Append(~esg, DiagonalMatrix(GF(q),[w4: i in [1..r]]));

  //esg now generates symplectic group of order p^(2n+2).

  //Now normaliser gens.
  esn := [gl|];
  //diagonals different for symplectic
  for i in [0..n-1] do
    d := [];
    for j in [1..p^(n-1-i)] do
      exp := 0;
      for k in [0..p-1] do
        exp +:= k;
        for l in [1..p^i] do Append(~d,w4^exp); end for;
      end for;
    end for;
    Append(~esn, DiagonalMatrix(GF(q),d));
  end for;

  for i in [0..n-1] do
    mat := MatrixAlgebra(GF(q),p^(i+1))!0;
    rno := 0;
    for j in [1..p^i] do
      for k in [0..p-1] do
         rno +:= 1;
         for l in [0..p-1] do
           mat[rno][j+l*p^i] := w^(k*l);
         end for;
      end for;
    end for;
    mat := DirectSum([mat : j in [1..p^(n-1-i)]]);
    Append(~esn, mat);
  end for;

  //Finally some permutation matrices that normalise it.
  R := sub< Sym(r) | dp >;
  for i in [2..n] do
    phi := hom< R->R | [R.1*R.i] cat [R.j : j in [2..n]] >;
    Append(~esn,PermutationMatrix(PermInducingAut(R,phi),GF(q)));
  end for;

  G := sub< gl | esg cat esn >; H := sub < gl | esg>;
  return G, H;

end function;
