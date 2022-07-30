
// G is already defined and will be given as an input to the algorithm. 

WordInGen := function(G, A) 

d := Dimension(G); 
GSLP := SLPGroup(4);
if d eq 1 then 
   return GSLP!1; 
end if; 

q := #BaseRing(G); 
F<omega> := GF(q); 
M := KMatrixSpace(GF(q), d, d); 
b := Basis(M); 
e := Factorization(q)[1][2];

// We now create the four generators. u, the two cycle; v, the n cycle; t an element that adds row / column 1 to row / column 2; delta, a generator to make the group over a prime power. 

u := M!Id(G) - b[1] - b[2] - b[d+2] + b[d+1]; 
u := G!u; 
v := b[d*d -d +1]; 
for i in [1..(d-1)] do 
   v := v - b[(i-1)*d + i + 1]; 
end for; 
v := G!v; 
t := M!Id(G) + b[2]; 
t := G!t; 
delta := M!Id(G) -b[1] -b[d+2] + omega*b[1] + (omega^-1)*b[d+2]; 
delta := G!delta; 
 	
B := Basis(F, PrimeField(F)); 
V, inc := VectorSpace(F, PrimeField(F)); 

/* We wish to find the matrix whose top row is [1 w 0 .. 0], has 1s on the leading diagonal and 0s everywhere else. t^delta gives us the matrix with [1 w^-2 0 .. 0] on the top row. You then wish to multiply t^delta by certain matrices to make the top row [1 w^b 0 .. 0] where b is odd. Conjugating this element by delta, takes 2 off b. Hence you conjugate this element by delta^((b-1)/2) to get [1 w 0 .. 0] on the top row.

We begin by multiplying by t to add 1 to the [1, 2] position until we get an odd power of w. If this fails to result in an odd power of t then we add combinations of 1 and even powers of w until we get an odd power of w in the [1, 2] place.

*/

if (Characteristic(F) eq q) or (q eq 4) then 
   a:= 0; 
   dp := 0;
else 
   a := 0; 
   dp := 0; // stand for delta power 
   k := 1; 
   while a eq 0 do 
      dp := dp +1; 
      if IsOdd(Log(dp + omega^-(2*k))) then 
         a := IntegerRing()!((Log(dp + omega^-(2*k)) - 1)/2); 
      end if; 
      if dp ge Characteristic(F) then 
         dp := 0; 
         k := k+1; 
      end if; 
      if (dp ge Characteristic(F)) and (k ge (q/2)) then 
         return "no result "; 
      end if; 
   end while; 
end if; 

O := ((t^delta)*t^dp)^(delta^a); 

S1 := GSLP!1;
S2 := GSLP!1;

OO := ((GSLP.2^GSLP.1)*GSLP.2^dp)^(GSLP.1^a);

// Need an if Log(1 + omega^-2) is odd statement here that gives us a different RowOp + Column Op depending on what we need. 

RowOp := function(i, j, A, r) 
if r eq 1 then 
   return t^(u*((v*u)^(j-i-1))*(v^(i-1)))*A; // only works when i < j - which is the only direction we ever need 
end if; 
if IsEven(r) then 
   return ((O^(delta^-IntegerRing()!((r-2)/2)))^(u*((v*u)^(j-i-1))*(v^(i-1))))*A; 
end if; 
if IsOdd(r) then 
   return (t^(delta^-IntegerRing()!((r-1)/2)))^(u*((v*u)^(j-i-1))*(v^(i-1)))*A; 
end if; 
end function; 

RowOpp := function(i, j, S, r) 
if r eq 1 then 
   return GSLP.2^(GSLP.3*((GSLP.4*GSLP.3)^(j-i-1))*(GSLP.4^(i-1)))*S; // only works when i < j - which is the only direction we ever need 
end if; 
if IsEven(r) then 
   return ((OO^(GSLP.1^-IntegerRing()!((r-2)/2)))^(GSLP.3*((GSLP.4*GSLP.3)^(j-i-1))*(GSLP.4^(i-1))))*S; 
end if; 
if IsOdd(r) then 
   return (GSLP.2^(GSLP.1^-IntegerRing()!((r-1)/2)))^(GSLP.3*((GSLP.4*GSLP.3)^(j-i-1))*(GSLP.4^(i-1)))*S; 
end if; 
end function; 

ColOp := function(i, j, A, r) 
if r eq 1 then 
   return A*t^(((v*u)^(j-i-1))*(v^(i-1))); 
end if; 
if IsEven(r) then 
   return A*((O^(delta^-IntegerRing()!((r-2)/2)))^(((v*u)^(j-i-1))*(v^(i-1)))); 
end if; 
if IsOdd(r) then 
   return A*(t^(delta^-IntegerRing()!((r-1)/2)))^(((v*u)^(j-i-1))*(v^(i-1))); 
end if; 
end function; 

ColOpp := function(i, j, S, r) 
if r eq 1 then 
   return S*GSLP.2^(((GSLP.4*GSLP.3)^(j-i-1))*(GSLP.4^(i-1))); 
end if; 
if IsEven(r) then 
   return S*((OO^(GSLP.1^-IntegerRing()!((r-2)/2)))^(((GSLP.4*GSLP.3)^(j-i-1))*(GSLP.4^(i-1)))); 
end if; 
if IsOdd(r) then 
   return S*(GSLP.2^(GSLP.1^-IntegerRing()!((r-1)/2)))^(((GSLP.4*GSLP.3)^(j-i-1))*(GSLP.4^(i-1))); 
end if; 
end function; 


A := G!A; 

// file 2 takes as input the random element A and gets 1 in the (1, 1) entry. 

Z := ZeroMatrix(GF(q), d, d); 
y := ZeroMatrix(IntegerRing(), d, 1); 
W := ZeroMatrix(GF(q), d, 2); 


for k in [1..d-1] do 

A := A^((v^-1)^(k-1)); // moves the first, second, …, kth  column and row out of the way 
S1 := (GSLP.4)^(k-1)*S1;
S2 := S2*((GSLP.4^-1)^(k-1));

if A[1, 1] eq 0 then 
i := 2; 
while A[1, i] eq 0 do 
   i := i+1; 
end while; 
A := A*(u*v^-1)^(i-2)*(u*v)^(i-2)*u; // swaps column 1 with column i, this will never move any columns that have already been done because they will always contain a 0 in the first row at this stage. 
y[k, 1] := i; 
S2 := S2*(GSLP.3*GSLP.4^-1)^(i-2)*(GSLP.3*GSLP.4)^(i-2)*GSLP.3;
end if; 

if A[1, 1] ne 1 then
   i := 2; 
   if {A[i, 1] eq 0 : i in [2..d]} eq {true} then
      A := A*(t^u);
      W[k, 2] := 1;
      S2 := S2*(GSLP.2^GSLP.3);
   end if;
   while A[i, 1] eq 0 do 
      i := i+1;
   end while;
   BB := (A[1, 1]-1)/A[i, 1];
   T := t^-1;
   TT := GSLP.2^-1;
   T := (T^(((v*u)^(i-2))))^IntegerRing()!inc(BB)[1];
   TT := (TT^(((GSLP.4*GSLP.3)^(i-2))))^IntegerRing()!inc(BB)[1];
   W[k, 1] := inc(BB)[1]; 
   for r in [2..e] do
      if IsEven(r) then 
         T := T*((((O^-1)^(delta^-IntegerRing()!((r-2)/2)))^(((v*u)^(i-2))))^IntegerRing()!inc(BB)[r]); 
         W[k, 1] := W[k, 1] + inc(BB)[r]*omega^(r-1); 
         TT := TT*((((OO^-1)^(GSLP.1^-IntegerRing()!((r-2)/2)))^(((GSLP.4*GSLP.3)^(i-2))))^IntegerRing()!inc(BB)[r]);
      end if; 
      if IsOdd(r) then 
         T := T*((((t^-1)^(delta^-IntegerRing()!((r-1)/2)))^(((v*u)^(i-2))))^IntegerRing()!inc(BB)[r]); 
         TT := TT*((((GSLP.2^-1)^(GSLP.1^-IntegerRing()!((r-1)/2)))^(((GSLP.4*GSLP.3)^(i-2))))^IntegerRing()!inc(BB)[r]);
         W[k, 1] := W[k, 1] + inc(BB)[r]*omega^(r-1); 
      end if;
   end for;
A := T*A;
S1 := TT*S1;
end if;


for j in [2..d-(k-1)] do 
for r in [1.. Factorization(q)[1][2]] do // needs to go up to the power of the characteristic of the field 
    while inc(A[j, 1])[r] ne 0 do 
       A := RowOp(1, j, A, r); 
       S1 := RowOpp(1, j, S1, r); 
       Z[j +(k-1), k] := Z[j+(k-1), k] +omega^(r-1); 
    end while; 
end for; 
end for; 

for j in [2..d-(k-1)] do 
for r in [1.. Factorization(q)[1][2]] do 
   while inc(A[1, j])[r] ne 0 do 
      A := ColOp(1, j, A, r);
      S2 := ColOpp(1, j, S2, r);
      Z[k, j+(k-1)] := Z[k, j+(k-1)] + omega^(r-1); 
   end while; 
end for; 
end for; 

A := A^(v^(k-1)); // moves the rows and colums back to their original position 

S1 := ((GSLP.4^-1)^(k-1))*S1;
S2 := S2*(GSLP.4^(k-1));

end for; 

return A, (S1^-1*S2^-1); 

end function; 

// Having completed the above, the A[d, d] entry should now be 1 too since the matrix will now have 1s along the main diagonal, zeroes everywhere else and the matrix must have determinant 1.

