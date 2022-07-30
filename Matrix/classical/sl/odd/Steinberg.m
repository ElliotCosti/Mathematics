// Converted from Steinberg.lm by MagmaCode 1.1 on Mon Jul 04 16:38:10 2005
//
// Matrix and word generators for SL(n,q)
// Author: Don Taylor
// Created:  29 June 2005
// Modified:  3 July 2005

SLElementToWord := function (G, E, W, g)

   F<a,b,c,d> := SLPGroup(4);
   
   SteinbergGL := function( A )
     error if Ncols(A) ne Nrows(A), "matrix must be square";
     m := Ncols(A);
     scalars := CoefficientRing(Parent(A)); // must be a field
     Ulist := [];
     Vlist := [];
     W := MatrixRing(scalars,m)!A;
     pivot := [ 0 : i in [1..m] ];
   
     for row := 1 to m do
       pivotcol := 0;
       for col := m to 1 by -1 do
         if W[row,col] ne 0 then
           if pivot[col] gt 0 then
             prow := pivot[col];
   
             t := W[row,col]/W[prow,col];
   
             W[row,col] := 0;
             Append(~Ulist,<row,prow,t>);
           else
             pivotcol := col;
             break;
           end if;
         end if;
       end for;
       error if pivotcol eq 0, "matrix must be non-singular";
       pivot[pivotcol] := row;
   
       for j := pivotcol-1 to 1 by -1 do
         if W[row,j] ne 0 then
           t := W[row,j]/W[row,pivotcol];
   
           W[row,j] := 0;
           for i := row+1 to m do
              W[i,j] -:= t*W[i,pivotcol];
           end for;
           Vlist := [<pivotcol,j,t>] cat Vlist;
         end if;
       end for;
     end for;
   
     return W,Ulist,Vlist;
   
   end function;
   
   /* first and 4th coincide with ours; second is inverse;
      our 3rd is obtained by conjugating this 3rd by 1st
      and then inverting */
   
   standardGen := function(n,q)
     K := GF(q);
     A := MatrixAlgebra(K,n);
     G := SL(n,K);
   
     M := Id(A);
     M[1,1] := 0;  M[1,2] := 1;
     M[2,1] := -1; M[2,2] := 0;
     a := G!M;
   
     M := Zero(A);
     M[n,1] := 1;
     for i := 2 to n do
       M[i-1,i] := -1;
     end for;
     b := G!M;
   
     M := Id(A);
     M[2,1] := 1;
     c := G!M;
   
     xi := PrimitiveElement(K);
     M := Id(A);
     M[1,1] := xi;
     M[2,2] := xi^-1;
     d := G!M;
     return a, b, c, d;
   end function;
   
   monomialToPerm := func< N |
     Sym(n)![ rep{ j : j in [1..n] | N[i,j] ne 0 } : i in [1..n] ]
       where n is Ncols(N) >;
   
   permToCoxWord := function( pi )
     w := [];
     W := Parent(pi);
     n := Degree(W) - 1;
   
     while pi ne Id(W) do
       i := rep{ j : j in [1..n] | (j+1)^pi lt j^pi};
       Append(~w,i);
       pi := W!(i,i+1)*pi;
     end while;
     return w;
   end function;
   
   WeylWord := func< w | #w eq 0 select Id(F) else &*[ a^(b^(i-1)) : i in w ] >;
   
   monomialToTorus := function(N)
     n := Ncols(N);
   
     transpositions := [];
     A := Parent(N);
     G := GL(n,CoefficientRing(A));
     for i := 1 to n-1 do
       M := Id(A);
       M[i,i] := 0;  M[i,i+1] := 1;
       M[i+1,i] := -1; M[i+1,i+1] := 0;
       Append(~transpositions, G!M);
     end for;
     cw := permToCoxWord(monomialToPerm(N));
     pmat := #cw eq 0 select Id(G)
       else &*[ transpositions[i] : i in cw ];
     h := N*pmat^-1;
     return [ i eq 1 select h[1,1] else Self(i-1)*h[i,i] : i in [1..n]];
   end function;
   
   torusWord := func< h | &*[ (d^Log(h[i]))^(b^(i-1)) : i in [1..#h] ] >;
   
   rootWord := function(n,root)
     i := root[1]; j := root[2]; xi := root[3];
     S := Sym(n);
     if i eq 2 then
       pi := j eq 1 select Id(S) else S!(1,j);
     elif j eq 1 then
       pi := S!(2,i);
     else
       pi := S!(2,i)(1,j);
     end if;
   
     e := (d*d^b)^Log(xi);
     m := WeylWord( permToCoxWord(pi) );
     return (c^e)^m;
   end function;
   
   unipotentWord := func< n,s |
          #s eq 0 select Id(F) else &*[ rootWord(n,i) : i in s ] >;
   
   matrixToWord := function(A)
     N,U,V := SteinbergGL(A);
     n := Ncols(A);
     ww := WeylWord(permToCoxWord(monomialToPerm(N)));
     hw := torusWord(monomialToTorus(N));
     uu := unipotentWord(n,U);
     vv := unipotentWord(n,V);
     return uu*hw*ww*vv;
   end function;
   
   /* 
   homFactory := function(n, q)
      aa,bb,cc,dd := standardGen(n,q);
      return hom< F->SL(n,q) | aa, bb, cc, dd >;
   end function;
       
   n := Degree (G); q := #BaseRing (G);
   phi := homFactory (n,q);
   */
       
   w := matrixToWord (g);
   
   /* convert Taylor standard generators to ours */
   tau := hom <F -> F | [a, b^-1, (c^(a))^-1, d]>;
   w := tau (w);
       
   /* rewrite in terms of user-supplied generators */
   P := Parent (W[1]);
   gamma := hom <F -> P | W>;
   return gamma (w);
      
end function;
   
/* 
   n := 6; q := 11;
   print "Testing with n =",n,"and q =",q;
   
   rootMatrix := function(n,root)
     xi := root[3];
     M := Id(MatrixAlgebra(Parent(xi),n));
     M[root[1],root[2]] := xi;
     return M;
   end function;
   
   S := SL(n,q);
   g := Random(S);
   time N,U,V := SteinbergGL(g);
   print "Monomial test:", IsMonomial(N);
   u := &*[rootMatrix(n,x) : x in U];
   v := &*[rootMatrix(n,x) : x in V];
   print "Reconstruction:",g eq u*N*v;
   
   print "Root tests (zero):",
     "U",  forall{ x : x in U | x[3] ne 0 },
     ", V",forall{ x : x in V | x[3] ne 0 };
   
   print "Positive root tests:",
     "U",  forall{ x : x in U | x[1] gt x[2] },
     ", V",forall{ x : x in V | x[1] gt x[2] };
   
   aa,bb,cc,dd := standardGen(n,q);
   S := SL(n,q);
   if n le 5 and q le 11 then
     time print "Generator test:", S eq sub<S|aa,bb,cc,dd>;
   end if;
   
   phi := homFactory(n,q);
   print phi(a) eq aa,phi(b) eq bb, phi(c) eq cc, phi(d) eq dd;
   
   pi := monomialToPerm(N);
   print pi;
   print "Negative root test for U and N:",
     forall{ x : x in U | x[1]^pi lt x[2]^pi };
   
   cw := permToCoxWord(pi);
   
   CoxWordToPerm := function( w, n )
     S := Sym(n);
     gen := [S!(i,i+1) : i in [1..n-1]];
     return #w eq 0 select Id(S) else &*[gen[i] : i in w];
   end function;
   print "Transposition check:", pi eq CoxWordToPerm(cw,n);
   
   h := monomialToTorus(N);
   print h;
   hh := DiagonalMatrix(GF(q),n,[h[1]] cat [h[i-1]^-1*h[i] : i in [2..n] ]);
   print "Weyl and torus check:",hh*phi(WeylWord(cw)) eq N;
   print "Determinants of h, N and pi:",
          Determinant(hh), Determinant(N), Sign(pi);
   
   ww := WeylWord( cw );
   hw := torusWord( h );
   phi(hw*ww) eq N;
   
   uu := unipotentWord(n,U);
   vv := unipotentWord(n,V);
   print "Image of U test:",phi(uu) eq u;
   print "Image of V test:",phi(vv) eq v;
   
   print "Testing matrixToWord:", phi(matrixToWord(g)) eq g;
   
   extendedTest := procedure(n,q,m)
     S := SL(n,q);
     phi := homFactory(n,q);
     for i := 1 to m do
       g := Random(S);
       w := matrixToWord(g);
       error if phi(w) ne g, "Failure";
     end for;
     print "Success";
   end procedure;
*/
