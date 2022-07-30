/* estimate order of g mod K^G */

OrderModulo := function (G, K, g: NumberRandom := 10)
   O := [];
   for j in [1..NumberRandom] do
      k := NormalSubgroupRandomElement (G, K);
      o := Order (g * k);
      Include (~O, o);
      if Gcd (O) eq 1 then return 1; end if;
   end for;
   return Gcd (O);
end function;

/* some elements of kernel */

ElementsOfKernel := function (P, n: Limit := 10, k := 2)

   L := [];
   repeat 
      u := Random (P);
      a := ExtractBlock (u, 1, 1, n, n);
      b := ExtractBlock (u, n+1, n+1, n, n);
      oa := Order (a); ob := Order (b);
      assert oa eq ob;
      o := Order (u);
      if o eq k * oa then Append (~L, u^(o div k)); end if;
   until #L gt Limit;

return L;
end function;

/* is action of group on both module composition 
   factors different? */

IsActionDifferent := function (P, n: Limit := 50, k := 2)
   nmr := 0;
   repeat 
      nmr +:= 1;
      u := Random (P);
      a := ExtractBlock (u, 1, 1,n, n);
      b := ExtractBlock (u, n+1, n+1, n, n);
      oa := Order (a); ob := Order (b); o := Order (u);
      if oa ne ob then return true; end if;
   until nmr gt Limit;
   return false;
end function;
