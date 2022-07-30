OddFPElt := function (b, wb, c, wc, n)
   if n le 3 then return b^0, wb^0; end if;
   x := c^(b^3); wx := wc^(wb^3);
   x := &*[x^(b^(2 * i)): i in [0..(n - 3) div 2 - 1]];
   wx := &*[wx^(wb^(2 * i)): i in [0..(n - 3) div 2 - 1]];
   return x, wx;
end function;

/* G is classical group of odd degree, even characteristic;
   E is its Steinberg basis; 
   construct odd order element which fixes some rows 
   of matrix and has no other fixed points; 
   option = 1: then fix botton 2 rows; 
   option = 2: then fix top 2 rows; 
   option = 3: fix no rows */

OddDegreeFPElt := function (G, E, W, option)

   if Degree (G) eq 3 then assert option eq 3; end if;

   b := E[2]^-1; wb := W[2]^-1;

   t := E[3]; wt := W[3];
   if option eq 2 then t := t^(b^2); wt := wt^(wb^2); end if;
   v := t^b;  wv := wt^wb;
   u := E[3]^E[1]; wu := W[3]^W[1];
   if option eq 2 then u := u^(b^2); wu := wu^(wb^2); end if;
   s := u^b; ws := wu^wb;

   /* element of order 7 in SL(3, 2) */
   x := v * t * u * s;
   wx := wv * wt * wu * ws;
   
   /* y has 3 x 3 identity block and multiple copies of  0 1 
                                                         1 1  */
   c := t * u;
   wc := wt * wu;
   if option in [1,2] then n := Nrows (b) - 2; else n := Nrows (b); end if;
   y, wy := OddFPElt (b, wb, c, wc, n);

   return x * y, wx * wy;
end function;

ProduceOddDegreeFPFElement := function (G, X, AX, A, WA, option) 
   g, wg := OddDegreeFPElt (AX, A, WA, option);
   wg := ImagesOfWords (AX, X, [wg])[1];
   wg := PullbackWord (G, X, wg);
   return g, wg;
end function;

/* a is 2-cycle, b is n-cycle;
   if option eq 1 return (n-2)-cycle on 1..n - 2 
   else return (n - 2)-cycle on 3..n */

EvaluateCycle := function (a, b, option)
   if option eq 1 then return b^2 * a * b * a * b^-1 * a * b * a * b^-2;
   else return a * b * a * b^-1 * a * b * a; end if;
end function;

/* delta is [lambda, 0, ... ; 0 lambda^-1, 0; ...] and b is n-cycle; 
   return element which acts fpf */

EvaluateFPElt := function (delta, b, n)
   if n le 0 then return delta^0; end if;
   if IsEven (n) then 
      return &*[delta^b^(2 * i): i in [0..n div 2 - 1]];
   else 
      error "Should not be here";
   end if;
end function;

/* produce an element of G which acts fixed-point freely on 
   1..m - 2 [if option is 1], else 3..m;

   if (m - 2)-cycle is not suppled, then compute it;
   X <= G and AX is composition factor describing X, AX is SL(m, q);
   A is Steinberg basis for AX and WA are corresponding words  */
  
ProduceFPF := function (G, X, AX, A, WA, m, option: cycle := false)

   if IsOdd (Degree (AX)) then 
       return ProduceOddDegreeFPFElement (G, X, AX, A, WA, option);
   end if;

   /* generator for (m - 2)-cycle */
   if cycle cmpeq false then 
      cycle := EvaluateCycle (A[1], A[2]^-1, option);
      wcycle := EvaluateCycle (WA[1], WA[2]^-1, option);
   else 
      wcycle := cycle[2]^-1;
      cycle := cycle[1]^-1;
   end if;

   wcycle := ImagesOfWords (AX, X, [wcycle])[1];
   wcycle := PullbackWord (G, X, wcycle);

   /* now produce odd order element acting fpf on 1.. m - 2 */
   delta := A[4];
   if option eq 2 then delta := delta^A[2]^2; end if;
   fpa := EvaluateFPElt (delta, cycle, m - 2); 
   wdelta := WA[4];
   if option eq 2 then wdelta := wdelta^WA[2]^2; end if;

   wdelta := ImagesOfWords (AX, X, [wdelta])[1];
   wdelta := PullbackWord (G, X, wdelta);
   wfpa := EvaluateFPElt (wdelta, wcycle, m - 2); 
   return fpa, wfpa;
end function;
