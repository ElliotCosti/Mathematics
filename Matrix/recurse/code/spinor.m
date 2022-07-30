/*
form should be bilinear, g is an element of the orthogonal group preserving
that form.  Even q uses the paper by Dye "the special orthogonal groups and
the Dickson invariant".  Odd q following Zassenhaus "on the  spinor norm"
returns 0 if g is in Omega, 1 if g is in SO \ Omega.
*/

intrinsic SpinorNorm(g::GrpMatElt, form::AlgMatElt) -> RngIntElt
{The spinor norm of the element in the special orthogonal group fixing the specified form}

  d:= NumberOfRows(g);
  q:= #BaseRing(g);
  assert IsEven(q) or g*form*Transpose(g) eq form;

  m:= MatrixAlgebra(GF(q), d);
  i:= Identity(m);

  //test from Dye paper.
  if IsEven(q) then
    r:= Rank(g - i);
    return IsEven(r) select 0 else 1;
  end if;

  assert IsOdd(q);
  a:= g + i;
  cp<x>:= CharacteristicPolynomial(a: Proof:= false);

//find the highest power of x that divides the CP. the nullspace of a to that power is the space //M(-1, \sigma) in the Zassenhaus paper
  exponent:= 0;
  while Coefficient(cp, exponent) eq 0 do
    exponent:= exponent+1;
  end while;

  if exponent gt 0 then
    cp:= ExactQuotient(cp, x^exponent);
    ns1:= Nullspace(a^exponent);
    basis1:= Basis(ns1);
    b1:= #basis1;  

  //this should be the form restricted to the nullspace
    list:= &cat[[Matrix(basis1[i])*form*Transpose(Matrix(basis1[j])) : j in [1..b1]]: i in [1..b1]];
    newform:= MatrixAlgebra(GF(q), b1)![x[1][1]: x in list];
    det1:= Determinant(newform);
  else det1:= GF(q)!1;
  end if;

//the nullspace of the remaining term in the CP is the space M^hat(-1, \sigma) in the Zassenhaus //paper
  if Degree(cp) gt 0 then
    ns2:= Nullspace(Evaluate(cp, a));
    basis2:= Basis(ns2);
    b2:= #basis2;
    newelt:= ScalarMatrix(d, GF(q)!2^(-1)) * a;

//this should be the matrix of 1/2(1+a) restricted to the subspace.
    newmat:= MatrixAlgebra(GF(q), b2)!&cat[Coordinates(ns2, basis2[i]*newelt) : i in [1..b2]];
    det2:= Determinant(newmat);
  else det2:= GF(q)!1;
  end if;

  return IsSquare(det1*det2) select 0 else 1;

end intrinsic;

intrinsic SpinorNorm(g::GrpMatElt, form::GrpMatElt) -> RngIntElt
{The spinor norm of the element in the special orthogonal group fixing the specified form}
 return SpinorNorm(g, Matrix(form));
end intrinsic;

/*********************************************************************/
//This function makes matrix entries that are needed for the
//conformal orthogonal group = normaliser of GO in GL.
function GetAandB(q)
  z:= PrimitiveElement(GF(q));
  for a in GF(q) do
    bool, b:= IsSquare(z - a^2);
    if bool then
      return a, b;
    end if;
  end for;
end function;

function COPlus(d, q)   
  assert IsEven(d);

  z:= PrimitiveElement(GF(q));
  prim_scal:= GL(d, q)!ScalarMatrix(d, z);
 
  if IsEven(q) then
    return sub<GL(d, q)|GOPlus(d, q), prim_scal>;
  end if;

  delta_plus:= GL(d, q)!DiagonalMatrix([z : i in [1..d div
    2]] cat [1 : i in [1..d div 2]]);
  return sub<GL(d, q)|GOPlus(d, q), delta_plus>;
end function;


function COMinus(d, q)
  assert IsEven(d);

  z:= PrimitiveElement(GF(q));
  gom:= GOMinus(d, q);
 
  if IsEven(q) then
    prim_scal:= GL(d, q)!ScalarMatrix(d, z);
    return sub<GL(d, q)|gom, prim_scal>;
  end if;

  b, form:= SymmetricBilinearForm(gom);
  //this matrix would conjugate gom into a group preserving the diagonal form given 
  //in kleidman and liebeck.
  mat:= GL(d, q)!CorrectForm(form, d, q, "orth-");
 
  if IsEven((d*(q-1)) div 4) then
    disc:= "nonsquare";
  else
    disc:= "square";
  end if;

  a, b:= GetAandB(q);  
  if disc eq "square" then
    delta:= GL(d, q)!Matrix(GF(q), d, d,
        &cat[[<2*i+1, 2*i+1, a>, <2*i+1, 2*i+2, b>,
         <2*i+2, 2*i+1, b>, <2*i+2, 2*i+2, -a>] : i in [0..((d div 2)-1)]]);
    //delta;
  else
    delta:= GL(d, q)!Matrix(GF(q), d, d,
       &cat[[<2*i+1, 2*i+1, a>, <2*i+1, 2*i+2, b>,
       <2*i+2, 2*i+1, b>, <2*i+2, 2*i+2, -a>] : i in [0..((d div 2)-2)]]
       cat [<d-1, d, 1>, <d, d-1, z>]);
    //delta;
  end if;

  return sub<GL(d, q)|GOMinus(d, q), delta^(mat^-1)>;
 
end function;
  
function CO(d, q)
  assert IsOdd(d);

  z:= PrimitiveElement(GF(q));
  return sub<GL(d, q)|GO(d, q), ScalarMatrix(d, z)>;
end function;
  

/**************************************************************************************/

//function to compute the map tau as given in Kleidman and Liebeck - measures how much an
//element of the conformal group warps the form. returns a nonzero field element lambda such that
//f(xg, yg) = lambda*f(x, y) for all vectors x, y. if lambda = 1 then g is in the orthogonal 
//group. 

function tmap(g, f, d, q)
  //find a pair of vectors e_x and e_y s.t. f(e_x, e_y) \neq 0. if the form is nondegenerate then
  // the first value of x will work for some y.
  found:= false;
  for x in [1..d] do
    if not found then
      for y in [1..d] do
        if not  (f[x][y] eq 0) then
          i:= x; j:= y; found:= true;
        end if;
      end for;
    end if;
  end for;
  list1:= [0 : x in [1..i-1]] cat [1] cat [0 : x in [i+1..d]];
  list2:= [0 : x in [1..j-1]] cat [1] cat [0 : x in [j+1..d]];

  //find images of e_x, e_y under g.
  v1:= (RSpace(GL(d, q))!list1)*g;
  v2:= (RSpace(GL(d, q))!list2)*g;
 
  return (Matrix(v1)*f*Transpose(Matrix(v2))*GL(1, q)![f[i][j]^-1])[1][1];
end function;

//function to compute the coset of an element of the conformal group, odd dimension odd field.
//returns a scalar matrix, a spinor norm value, and an element g1 of SO, such that g1*scalar
//is the original element, and the spinor norm value is the norm on g1. 

function ExtendedSpinorNormOddOdd(g, f, d, q)
  //fixing the tmap with a scalar gets us into the orthogonal group.
  t:= tmap(g, f, d, q);
  rt:= Root(t, 2);
  scal1:= ScalarMatrix(d, rt);
  
  //now fix determinant +/-1 to get into SO
  if Determinant(g)*Determinant(scal1)^-1 eq GF(q)!-1 then
    scal2:= ScalarMatrix(d, GF(q)!-1);
  else 
    scal2:= GL(d, q).0;
  end if;

  //finally do spinor norm on the elt of GO. elements can be described by spinor norm and a 
  //pair of scalars.
  g1:= scal1^-1 * scal2^-1 * g;

  return scal1, scal1[1][1], scal2, scal2[1][1], g1, SpinorNorm(g1*scal2, f);
end function;

function ExtendedSpinorNormEvenEven(g, f, d, q)
  //fixing the tmap with a scalar gets us into the orthogonal group.
  t:= tmap(g, f, d, q);
  rt:= Root(t, 2);
  scal1:= ScalarMatrix(d, rt);
  
  //finally do spinor norm on the result. elements can be described by spinor norm and a scalar.
  g1:= scal1^-1 * g;

  return scal1, scal1[1][1], GL(d, q).0, GF(q)!1, g1, SpinorNorm(g1, f);
end function;
  

function ExtendedSpinorNormEvenOdd(g, f, d, q, sign)
 //K&L need the form to be diagonal. our input form may not be, AND the one preserved by 
 //magma is not, but the form mapped to by CorrectForm is (although it has final entry a 
 //primitive field element rather than first one.
  if sign eq "orthogonalplus" then
    matfplus:= CorrectForm(f, d, q, "orth+");
    b, f1:= SymmetricBilinearForm(GOPlus(d, q));
    matcoplus:= CorrectForm(f1, d, q, "orth+");
  else
    matfminus:= CorrectForm(f, d, q, "orth-");
    b, f1:= SymmetricBilinearForm(GOMinus(d, q));
    matcominus:= CorrectForm(f1, d, q, "orth-");
    b, newform:= SymmetricBilinearForm(GOMinus(d, q)^matcominus);
    //"newform =", newform;
  end if;

  //fixing the tmap with a power of delta gets us into the orthogonal group.
  t:= tmap(g, f, d, q);
  if t eq 1 then
    delta:= GL(d, q).0;
    g1:= g;
  elif sign eq "orthogonalplus" then
    //this version of delta works for GOPlus as in magma.
    delta:= GL(d, q)!DiagonalMatrix([t : i in [1..d div 2]] cat [1 : i in [1..d div 2]]);
    delta:= delta^(matcoplus*matfplus^-1);
    g1:= delta^-1 * g;
  else //minus type is more complicated
    bool, b:= IsSquare(t);
    if bool then //discriminant square or nonsquare comes out the same if t is square.
      //"t square";
      delta:= ScalarMatrix(d, b);
      t1:= tmap(delta, GL(d, q).0, d, q);
      if not (t1 eq t) then //taken wrong square root
        delta:= delta*ScalarMatrix(d, GF(q)!-1);
        assert tmap(delta, GL(d, q).0, d, q) eq t;
      end if;
    else 
      //"t nonsquare, t is", t;
      z:= PrimitiveElement(GF(q));
      bool, c:= IsSquare(t*z^-1);
      assert bool;
      a, b:= GetAandB(q);
      if IsEven((d*(q-1)) div 4) then //discriminant nonsquare
        //"disc nonsquare";
        delta1:= GL(d, q)!Matrix(GF(q),d,d, &cat[[<2*i+1, 2*i+1, a*c>, <2*i+1, 2*i+2, b*c>,
         <2*i+2, 2*i+1, b*c>, <2*i+2, 2*i+2, -a*c>] : i in [0..((d div 2)-2)]]  
          cat [<d-1, d, c>, <d, d-1, z*c>]);
        t1:= tmap(delta1^(matcominus^-1), f1, d, q);
        //"t1 is", t1;
        if not (t1 eq t) then //found wrong square root
          delta1:= delta1*ScalarMatrix(d, GF(q)!-1);
          //"new delta1 =", delta1; 
        end if;
        //assert delta1^(matcominus^-1)*f1*Transpose(delta1^(matcominus^-1)) eq ScalarMatrix(d, t)*f1;
     else 
        delta1:= GL(d, q)!Matrix(GF(q), d,d, &cat[[<2*i+1, 2*i+1, a*c>, <2*i+1, 2*i+2, b*c>,
         <2*i+2, 2*i+1, b*c>, <2*i+2, 2*i+2, -a*c>] : i in [0..((d div 2)-1)]]);  
         t1:= tmap(delta1, GL(d, q).0, d, q);
        if not (t1 eq t) then //found wrong square root
          delta1:= delta1*ScalarMatrix(d, GF(q)!-1); 
        end if;
      end if;
      //assert tmap(delta1, newform, d, q) eq t;
      delta:= delta1^(matfminus^-1);
      //assert delta*f*Transpose(delta) eq ScalarMatrix(d, t)*f;
    end if;
    //assert tmap(delta, f, d, q) eq t;
    g1:= delta^-1 * g;
  end if;

  //assert tmap(g1, f, d, q) eq GF(q)!1;
 
  spin:= SpinorNorm(g1, f);

  if Determinant(g1) eq 1 then
    g2:= GL(d, q).0;
  else
    g2:= GL(d, q)!Matrix(GF(q), d, d, [<1, d, -2>, <d, 1, -1*GF(q)!(2^-1)>] cat [<i,i,1> : i in [2..d-1]]);
    if sign eq "orthogonalminus" then
      g2:= g2^(matcominus*matfminus^-1);
    else
      g2:= g2^(matcoplus*matfplus^-1);
    end if;
  end if;

  g3:= g2^-1 * g1;

  //assert Determinant(g3) eq 1 and g3*f*Transpose(g3) eq f;
  //assert delta*g2*g3 eq g;

  return delta, t, g2, Determinant(g1), g3, spin;
end function;


//the extended spinor norm decomposes the matrix g into: a diagonal element, an element of GO but 
//not SO, and an element of SO. returns up to 6 things: the diagonal elt, the field element
//describing it (see the t-map for more details when the diagonal is not scalar), a reflection
//(or the identity), a flag +/- 1 to indicate whether the preceding elt is the identity, an elt 
//of SO and the (standard) spinor norm of the product of the reflection and the elt of SO 
//sometimes the reflection is never needed 
//(whenever q is even or d is odd), in which case the middle two values are placeholders.
//sign only needs to be completed for even dimension odd field, should be "orthogonalplus" or
//"orthgonalminus"
function ExtendedSpinorNorm(g, f, sign)
  d:= NumberOfRows(g);
  q:= #BaseRing(g);

  if IsOdd(d) then
    assert IsOdd(q);
    return ExtendedSpinorNormOddOdd(g, f, d, q);
  elif IsEven(d) and IsEven(q) then
    return ExtendedSpinorNormEvenEven(g, f, d, q);
  else
    return ExtendedSpinorNormEvenOdd(g, f, d, q, sign);
  end if;
end function;

InOmega := function(g,d,q,sign)
  local isf, form;
  if sign eq 1 then
    if d eq 2 then form := Matrix(GF(q),2,2,[0,1,1,0]);
    else isf, form := SymmetricBilinearForm(GOPlus(d,q));
    end if;
  elif sign eq -1 then
    isf, form := SymmetricBilinearForm(GOMinus(d,q));
  else
    isf, form := SymmetricBilinearForm(GO(d,q));
  end if;
  return SpinorNorm(GL(d,q)!g,form) eq 0;
end function;
