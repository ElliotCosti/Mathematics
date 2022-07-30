import "C:/Program Files/magma/package/Group/GrpMat/sl2q/decompose.m":
ScaleFactor;

import "C:/Program Files/magma/package/Group/GrpMat/sl2q/natural.m":
ConstructSL2Basis;
// forward RecognizeSL2;

/* if x is an element of a leafnode G, return the corresponding
   element word of the black-box group for G */

SLPImage := function (G, x)

   vprint User3: "now in SLPImage";
   if not (x in G) then return false, _; end if;

   B := G`SLPGroup;
   tau := G`InverseWordMap;
   return true, tau (x);

end function;

/* process G using centraliser strategy? */

RybaGroup := function (G: Limit := 10^4)

   if IsTrivial (G) then return false; end if;
   p := Characteristic (BaseRing (G));
   if IsEven (p) then return false; end if;
   if (Degree (G) le 8 and #BaseRing (G) le 9) then return false; end if;
   if Degree (G) gt 80 or
   (Degree (G) ge 3 and IsAbsolutelyIrreducible (G) and 
    RecognizeClassical (G) eq true) then
"HERE IN RYBAGROUP";
      return true;
   end if;

   return false;

   if Type(G) ne GrpMat then return false, _; end if;
   if Degree (G) eq 1 then return false, _; end if;
   B := GoodBasePoints (G);
   if #B eq 0 then return false, _; end if;
   d, F := BasicParameters (G);
   U := sub <VectorSpace (F, d) | B[1]>;
   l, u, s := EstimateOrbit (G, U: MaxSize := Isqrt (Limit));
   return (l gt Limit) or (s eq 0), s;
end function;

/* store inverse word map for G */
procedure SetupMatrixLeaf (G)
   vprint User3: "now in SetupMatrixLeaf";
   B := G`SLPGroup;
   RandomSchreier (G: Run := 60);
   U := UserGenerators (G);
   tau := InverseWordMap (G);
   index := [Position (U, G.i): i in [1..Ngens (G)]];
   // "index is ", index;
   S := Image (tau);
   eta := hom <S -> B | [B.i: i in index]>;
   G`InverseWordMap := tau * eta;
end procedure;

/* our node is isomorphic to <G, alpha> / <alpha>;
   a leaf has determinant 1 but the generators listed may not have; 
   scale them first and store the scaled group as a component of G; 
   otherwise membership testing goes wrong */

RecognizeGroupAsSLd2 := function (G) 

   flag := IsSL2Group (G);

   if flag cmpeq false then return false, _; end if;
   if flag cmpeq true then return true, _; end if;
   
   d := Degree (G);

   if d eq 1 then G`SL2Flag := false; return false; end if;

//   if IsProbablyPerfect (G) eq false then return false; end if;

/* 
   if d gt 2 
      classical := RecognizeClassical (G); 
      G`SL2Flag := false; return false; 
   end if;
*/

/* 
   if classical cmpeq true and d gt 2 then 
      G`SL2Flag := false; return false; 
   end if;
*/

   if d eq 2 then 
      classical := RecognizeClassical (G); 
      if classical then 
         H, scale := ScaleFactor (G);
         if Type (H) eq BoolElt then return false, _; end if;
         flag := ConstructSL2Basis (H);
         G`SL2Flag := flag; 
         if flag eq false then return false; end if;
         if scale then 
            G`SLPGroup := H`SLPGroup;
            U := UserGenerators (G);
            G`SLPGroupHom := MyHom (G, G`SLPGroup, U);
            G`SL2Group := H;
         end if;
         return true;
      else 
         return false, _; 
      end if;
   end if;
   
   F := BaseRing (G);
   p := Characteristic (F);

   if IsProbablyPerfect (G) eq false then 
      G`SL2Flag := false; return false;
   end if;

   flag, name := LieType (G, p); 
   if flag cmpeq true and (name[1] eq "A" and name[2] eq 1) then
      vprint User1: "Leaf contains SL2, name ", name;
      flag := RecognizeSL2 (G);
      G`SL2Flag := flag; 
      return flag;
   end if;
   
   return false;
end function;

/* solve the word problem for a leaf node */

procedure WordProblemForLeaf (~node)

   vprint User3: "now in WordProblemForLeaf";

   G := GroupOfNode (node); 
   U := UserGenerators (G);
   B := G`SLPGroup;

   /* set up inverse word map from user-generators of G 
      to SLP group on user-generators */
   if Type (G) eq GrpMat then 
      /* if the group is SL2 in natural repn, use special machinery */
      if RecognizeGroupAsSLd2 (G) then 
         vprint User1: "SL2 group node";
         G`Ryba := false; 
      else 
         flag := RybaGroup (G);
         G`Ryba := flag; 
         if not IsRybaGroup (G) then 
           // SetupMatrixLeaf (G);
           T := CompositeMatrixLeaf (G);
           G`CompSeries := T;
         end if;
      end if;
   elif Type (G) eq GrpPC then 
      // "1st Call creating perm rep for p-group";
      // gamma, C := CosetAction (G, sub <G | >);
      // s := sub <C | [gamma (u): u in U]>;
      // delta := InverseWordMap (s);
      // G`InverseWordMap := gamma * delta;
      T := CompositePCLeaf (G);
      G`CompSeries := T;
   elif Type (G) eq GrpPerm then 
      // delta := InverseWordMap (G);
      // G`InverseWordMap := delta;
      T := CompositePermLeaf (G);
      G`CompSeries := T;
   elif Type (G) eq GrpAb then 
      vprint User1: "Cyclic group node";
      T := CompositeAbelianLeaf (G);
      G`CompSeries := T;
   else 
      error "WordProblemForLeaf: Type of G";
   end if;

   node`group := G;

   vprint User1: "now finished in WordProblemForLeaf";

end procedure;
