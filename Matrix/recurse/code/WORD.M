forward ElementsSatisfyAschbacher;
forward Ryba;

import "C:/Program Files/magma/package/Group/GrpMat/sl2q/decompose.m":ScaleMatrix;

/* if g is an element of G = SL2 in natural repn, 
   express g as word in user generators;

   it is possible that only a scaled version of G is SL(2, q);
   for example if G is one of the factors from a tensor product;
   if so, a scaled SL2 should already be stored in G */

MySL2ElementToWord := function (G, g)
   if Degree (G) eq 2 then 
      if Determinant (g) ne 1 and not assigned G`SL2Group then 
         "Input group is not SL2"; 
         return false, _; 
      end if;
      if assigned G`SL2Group then GG := G; G := G`SL2Group; end if;
      if Determinant (g) ne 1 then gg := g; g := ScaleMatrix (g); end if;
      if Type (g) cmpeq BoolElt then return false, _; end if;
   end if;
/* temp -- will need fixing for new version of SL2ElementToWord */
   flag, w := SL2ElementToWord (G, GL(Degree (G), BaseRing (G))!g);
// flag := w;
   if flag cmpeq false then return false, _; end if;

   /* G embedded over larger field may be tensor-decomposable;
      if so, w in wrong SLPGroup */
   if assigned G`TensorFactors then
      basis := TensorBasis (G);
      if BaseRing (Parent (basis)) ne BaseRing (G) then
         W := G`SLPGroup;
         tau := hom <Parent (w) -> W | [W.i: i in [1..Ngens (W)]]>;
         w := tau (w);
      end if;
   end if;

   return true, w; 
end function;
 
/* evaluate word in G */

EvaluateWord := function (G, word)

   P := Parent (word);
   B := G`SLPGroup;
   m := Ngens (P); 
   alpha := hom <P -> B | [B.i : i in [1..m]]>;
   word := alpha (word);
   gamma := G`SLPGroupHom;
   return gamma (word), word;
end function;

/* given words (as straightline programs) in G; 
   return image of these in H, whose generators
   are in 1-1 correspondence with those of G */

ImagesOfWords := function (G, H, words)
   BG := G`SLPGroup;
   BH := H`SLPGroup;
BG, BH;
   assert Ngens (BG) eq Ngens (BH);
   m := Ngens (BH); 
   alpha := hom <BG -> BH | [BH.i : i in [1..m]]>;
   return [alpha (w): w in words];
end function;

/* express g as a word in group of node */

SolveWord := function (A, node, g: Factor := [0,0])

   if Factor ne [0,0] then factor := Factor; else factor := [0,0]; end if;

   G := GroupOfNode (node);

   if not IsLeaf (node) then 
      vprint User2: "Here test of Aschbacher category";
      if ElementsSatisfyAschbacher (G, [g]) eq false then 
         "1 Element doesn't satisfy Aschbacher class";
         return false, node`identifier, _; 
      end if;
   end if;

   if IsLeaf (node) then 
      A[node`identifier] := node;
      if IsRybaGroup (G) then 
         vprint User1: "Call Centraliser of Involution procedure";
         flag, word := Ryba (G, g);
      elif IsSL2Group (G) cmpeq true then
         // vprint User1: "Call SL2 procedure";
         flag, word := MySL2ElementToWord (G, g);
      elif Type (G) eq GrpAb then  
         flag, word := SolveWordCyclicGroup (G, g);
      else 
         flag, word := SLPImage (G, g);
      end if;
      if flag cmpeq false then 
         return false, [node`identifier, 1], _;
      else 
         if Factor eq [0,0] and not IsIdentity (g) then 
            return true, word, [node`identifier, 1];
         else 
            return true, word, Factor;
         end if;
      end if;
   end if;

   if RightChildOfNode (node) cmpeq false then 
      return "unknown", "";
   else 
      I := A[RightChildOfNode (node)];
   end if;

   /* solve for the right child */
   image := ConstructImage (G, g);
   flag, iword, identifier := $$ (A, I, image: Factor := factor);

   /* record first composition factor where image is non-trivial */
   if assigned identifier then 
      // "image is ", image;
      // "Identifier is ", identifier;
      if factor eq [0,0] then 
         factor := identifier;
         // "factor is ", factor;
      end if;
   end if;

   if flag cmpeq false or flag cmpeq "unknown" then 
      return flag, iword, Factor;
   end if;

   /* now consider left child */
   if LeftChildOfNode (node) cmpeq false then
      return "unknown", "", _;
   else 
      K := A[LeftChildOfNode (node)];
   end if;

   im, iword := EvaluateWord (G, iword); 

   k := g * im^-1;

   flag, word2, Factor := $$ (A, K, k: Factor := factor);
   if flag cmpeq false or flag cmpeq "unknown" then 
      return flag, word2, Factor;
   end if;

   /* rewrite word2, an element of kernel, as word in 
      generators of G */
   P := G`SLPGroup;
   theta := hom <Parent (word2) -> P | GroupOfNode (K)`UserWords>;
   return true, theta (word2) * iword, Factor;

end function;
