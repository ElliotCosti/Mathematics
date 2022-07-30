
SymplecticWordInGen := function(G, A);

d := Dimension(G);
q := #BaseRing(G);
F<w> := BaseRing(G);
w := PrimitiveElement(F);
G := SL(d, q);
_, inc := VectorSpace(F, PrimeField(F));
e := Factorisation(q)[1][2];

M := KMatrixSpace(GF(q), d, d);
V := VectorSpace(GF(q), d);
b := Basis(M);

CB := ZeroMatrix(GF(q), d, d);
for i in [1..IntegerRing()!(d/2)] do
   CB := CB + b[(i-1)*d + 2*i - 1];
end for;
for i in [1..IntegerRing()!(d/2)] do
   CB := CB + b[IntegerRing()!(d/2)*d + i*d - 2*i + 2];
end for;
   CB := SL(d, q)!CB;

A := G!(A^CB);

if d ne 2 then
   u := M!Id(G) - b[1] - b[d+2]- b[(d-1)*d-1] - b[d*d] + b[2] + b[d+1] + b[(d-1)*d] + b[d*d-1];
      u := G!u;
else
   u := -b[2]+b[3];
end if;

v := ZeroMatrix(GF(q), d, d);
for i in [1..IntegerRing()!(d/2 - 1)] do
   v := v + b[(2*i-2)*d + 2*i + 1];
end for;
v := v + b[d*d - 2*d + 1];
for i in [1..IntegerRing()!(d/2 -1)] do
   v := v + b[(2*i -1)*d + 2*i + 2];
end for;
v := v + b[d*d - d + 2];
   v := SL(d, q)!v;

x := M!Id(G) + b[d+3] + b[3*d+1];
   x := G!x;

t := M!Id(G) + b[d];
   t := G!t;

delta := M!Id(G) - b[1] - b[d*d] + w*b[1] + (w^-1)*(b[d*d]);
   delta := G!delta;

delta := delta^CB;
t := t^CB;
u := u^CB;

s := M!Id(G) - b[1] - b[2] - b[d+2] + b[d+1]; 
   s := G!s; 

GG := sub<SL(d, q)|delta, s, t, u, v, x>;
SLP := SLPGroup(6);
S1 := Id(SLP);
S2 := Id(SLP);

if (Characteristic(F) eq q) or (q eq 4) then 
   a:= 0; 
   dp := 0;
else 
   a := 0; 
   dp := 0; // stand for delta power 
   k := 1; 
   while a eq 0 do 
      dp := dp +1; 
      if IsOdd(Log(dp + w^-(2*k))) then 
      a := IntegerRing()!((Log(dp + w^-(2*k)) - 1)/2); 
      end if; 
      if dp ge Characteristic(F) then 
         dp := 0; 
         k := k+1; 
      end if; 
      if (dp ge Characteristic(F)) and (k ge (q/2)) then 
         error "no result "; 
      end if; 
   end while; 
end if; 

O := ((t^delta)*t^dp)^(delta^a);
OO := ((SLP.3^SLP.1)*SLP.3^dp)^(SLP.1^a);
block := IntegerRing()!(d/2); // the number of blocks

/* BB is an element of GF(q). This algorithm returns the transvection with BB in the [2, 1] position */

GetBBTransvection := function(BB);

   T := t^-1;
   TT := SLP.3^-1;
   T := (T^s)^IntegerRing()!inc(BB)[1];
   TT := (TT^SLP.2)^IntegerRing()!inc(BB)[1];

   for r in [2..e] do
      if IsEven(r) then
         o := O^-1;
         oo := OO^-1;
         o := o^(delta^-IntegerRing()!((r-2)/2));
         oo := oo^(SLP.1^-IntegerRing()!((r-2)/2));
         o := (o^s)^IntegerRing()!inc(BB)[r];
         oo := (oo^SLP.2)^IntegerRing()!inc(BB)[r];
         T := T*o;
         TT := TT*oo;
      else
         o := t^-1;
         oo := SLP.3^-1;
         o := o^(delta^-IntegerRing()!((r-1)/2));
         oo := oo^(SLP.1^-IntegerRing()!((r-1)/2));
         o := (o^s)^IntegerRing()!inc(BB)[r];
         oo := (oo^SLP.2)^IntegerRing()!inc(BB)[r];
         T := T*o;
         TT := TT*oo;
      end if;
   end for;

   return T, TT;

end function;

for k in [1..block] do

/* what happens if A[1, 1] is 0 */

if A[1, 1] eq 0 then 
   i := 2; 
   while A[1, i] eq 0 do 
      i := i+1; 
   end while;
   if IsEven(i) then j := IntegerRing()!(i/2);
   else j := IntegerRing()!(i/2 + 1/2); end if;
   if i eq 2 then
      A := A*s;
      S2 := S2*SLP.2;
   else
      A := A*(u*v^-1)^(j-2)*(u*v)^(j-2)*u; // swaps block 1 with block j, this will never move any columns that have already been done because those columns will always contain a 0 in the first row at this stage.
      S2 := S2*(SLP.4*SLP.5^-1)^(j-2)*(SLP.4*SLP.5)^(j-2)*SLP.4;
   end if;
   if A[1, 1] eq 0 then
      A := A*s;
      S2 := S2*SLP.2;
   end if;
end if; 

if A[1, 1] ne 1 then
   i := 2;
   while A[1, i] eq 0 do 
      i := i+1;
      if i eq d+1 then break; end if;
   end while;
   if i eq d+1 then
      z := Log(1/A[1, 1]);
      A := delta^z * A;
      S1 := SLP.1^z * S1;
   end if;
   if i eq 2 then

      BB := (1-A[1, 1])/A[1, 2];
      T, TT := GetBBTransvection(BB);
      A := A*T;
      S2 := S2*TT;

   elif i eq d+1 then
      A := A;
   else
      BB := (1-A[1, 1])/A[1, i];
      T, TT := GetBBTransvection(BB);

      if IsEven(i) then j := IntegerRing()!(i/2);
      else j := IntegerRing()!(i/2 + 1/2); end if;
      if j eq 2 then
         A := A;
      else
         A := A*(u*v^-1)^(j-2)*(u*v)^(j-2)*(u*v^-1)^(j-2)*(u*v)^(j-2)*u; // swaps block 2 with block j
         S2 := S2*(SLP.4*SLP.5^-1)^(j-2)*(SLP.4*SLP.5)^(j-2)*(SLP.4*SLP.5^-1)^(j-2)*(SLP.4*SLP.5)^(j-2)*SLP.4;
      end if;
      A := A*s; // puts the entry you wish to make equal to 1 in A[1, 2]
      S2 := S2*SLP.2;
      A := A*u; // puts the entry you wish to make equal to 1 in A[1, 4]
      S2 := S2 * SLP.4;
      if IsEven(i) then 
         A := A*x;
         S2 := S2*SLP.6;
      else
         A := A*s*x*(s^-1);
         S2 := S2*SLP.2*SLP.6*(SLP.2 ^-1);
      end if;
      A := A*(u^-1);
      S2 := S2*(SLP.4 ^-1);
      A := A*(s^-1);
      S2 := S2*(SLP.2 ^-1);
      if j ne 2 then
         A := A*(((u*v^-1)^(j-2)*(u*v)^(j-2)*(u*v^-1)^(j-2)*(u*v)^(j-2)*u)^-1);
         S2 := S2*(((SLP.4*SLP.5^-1)^(j-2)*(SLP.4*SLP.5)^(j-2)*(SLP.4*SLP.5^-1)^(j-2)*(SLP.4*SLP.5)^(j-2)*SLP.4)^-1);
      end if;
      BB := (1-A[1, 1])/A[1, 2];
      T, TT := GetBBTransvection(BB);
      A := A*T;
      S2 := S2*TT;
   end if;
end if;


A := A*s; // swaps first two columns
S2 := S2*SLP.2;

for l in [1..block-1] do

/* killing the [1, 3] place */
for r in [1..e] do
   S2 := S2*((SLP.6^(SLP.1^(r-1)))^IntegerRing()!inc(A[1, 3])[r]);
   A := A*((x^(delta^(r-1)))^IntegerRing()!inc(A[1, 3])[r]);
end for;

A := A*u*s*u; // swaps the third and fourth columns so that we can work on the f part of the block.
S2 := S2*SLP.4*SLP.2*SLP.4;

for r in [1..e] do
   S2 := S2*((SLP.6^(SLP.1^(r-1)))^IntegerRing()!inc(A[1, 3])[r]);
   A := A*((x^(delta^(r-1)))^IntegerRing()!inc(A[1, 3])[r]);
end for;

A := A*((u*s*u)^-1); // swaps the third and fourth columns back again
S2 := S2*((SLP.4*SLP.2*SLP.4)^-1);
A := A*(v*u); // vu is the (2..d/2) cycle on the blocks
S2 := S2*(SLP.5*SLP.4);

end for;

A := A*(s^-1); // swaps first two columns back again
S2 := S2*(SLP.2^-1);

S2 := S2*(SLP.3^IntegerRing()!-inc(A[1, 2])[1]);
A := A*(t^IntegerRing()!-inc(A[1, 2])[1]);
T := Id(G);
TT := Id(SLP);
for r in [2..e] do
   if IsEven(r) then
      o := O^(delta^-IntegerRing()!((r-2)/2));
      oo := OO^(SLP.1^-IntegerRing()!((r-2)/2));
      o := o^IntegerRing()!inc(A[1, 2])[r];
      oo := oo^IntegerRing()!inc(A[1, 2])[r];
      T := T*o;
      TT := TT*oo;
   else
      o := t^(delta^-IntegerRing()!((r-1)/2));
      oo := SLP.3^(SLP.1^-IntegerRing()!((r-1)/2));
      o := o^IntegerRing()!inc(A[1, 2])[r];
      oo := oo^IntegerRing()!inc(A[1, 2])[r];
      T := T*o;
      TT := TT*oo;
   end if;
end for;
A := A*(T^-1);
S2 := S2*(TT^-1);

/* now we do the second row */

A := s*A; // swaps the first two rows
S1 := SLP.2*S1;

for l in [1..block-1] do

for r in [1..e] do
   S2 := S2*((SLP.6^(SLP.1^(r-1)))^IntegerRing()!inc(A[1, 3])[r]);
   A := A*((x^(delta^(r-1)))^IntegerRing()!inc(A[1, 3])[r]);
end for;
A := A*u*s*u; // swaps the third and fourth columns so that we can work on the f part of the block.
S2 := S2*SLP.4*SLP.2*SLP.4;
for r in [1..e] do
   S2 := S2*((SLP.6^(SLP.1^(r-1)))^IntegerRing()!inc(A[1, 3])[r]);
   A := A*((x^(delta^(r-1)))^IntegerRing()!inc(A[1, 3])[r]);
end for;
A := A*((u*s*u)^-1); // swaps the third and fourth columns back again
S2 := S2*((SLP.4*SLP.2*SLP.4)^-1);
A := A*(v*u); // vu is the (2..d/2) cycle on the blocks
S2 := S2*(SLP.5*SLP.4);

end for;

A := A*(s^-1); // swaps first two columns back again
S2 := S2*(SLP.2 ^-1);
S2 := S2*(SLP.3^IntegerRing()!-inc(A[1, 2])[1]);
A := A*(t^IntegerRing()!-inc(A[1, 2])[1]);
T := Id(G);
TT := Id(SLP);
for r in [2..e] do
   if IsEven(r) then
      o := O^(delta^-IntegerRing()!((r-2)/2));
      oo := OO^(SLP.1^-IntegerRing()!((r-2)/2));
      o := o^IntegerRing()!inc(A[1, 2])[r];
      oo := oo^IntegerRing()!inc(A[1, 2])[r];
      T := T*o;
      TT := TT*oo;
   else
      o := t^(delta^-IntegerRing()!((r-1)/2));
      oo := SLP.3^(SLP.1^-IntegerRing()!((r-1)/2));
      o := o^IntegerRing()!inc(A[1, 2])[r];
      oo := oo^IntegerRing()!inc(A[1, 2])[r];
      T := T*o;
      TT := TT*oo;
   end if;
end for;
A := A*(T^-1);
S2 := S2*(TT^-1);

A := A^(v^-1);
S2 := S2*(SLP.5^-1);
S1 := (SLP.5)*S1;

end for;

return A, (S1^-1)*(S2^-1);

end function;

