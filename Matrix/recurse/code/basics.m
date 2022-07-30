/* definition of node record format */

forward InitialiseGroup;

NodeRF := recformat <group , type : MonStgElt,
                     parent: RngIntElt, identifier: RngIntElt, 
                     left: RngIntElt, right: RngIntElt>;

/* create node */

CreateNode := procedure (G, nodetype, parentid, id, ~node)
   node := rec < NodeRF | group := G, type := nodetype, parent := parentid,
                          identifier := id>; 
end procedure;

SLPGroupHom := function (node)
   if Type (node) eq Rec and assigned node`group then 
      node := node`group; 
   end if;
   if assigned node`SLPGroupHom then 
      return node`SLPGroupHom; 
   else 
      return "unknown"; 
   end if;
end function;

IsLeaf := function (node)
   if assigned node`type then 
      return node`type eq "leaf"; 
   else 
      return "unknown"; 
   end if;
end function;

GroupOfNode := function (node)
   return node`group;
end function;

ParentOfNode := function (node)
   return node`parent;
end function;

LeftChildOfNode := function (node)
   if assigned node`left then 
      return node`left; 
   else 
      return false;
   end if;
end function;

RightChildOfNode := function (node)
   if assigned node`right then 
      return node`right; 
   else 
      return false;
   end if;
end function;

CentraliserTrees := function (node)
   if assigned node`CentraliserTrees then 
      return node`CentraliserTrees; 
   else 
      return false;
   end if;
end function;

DisplayNode := function (node)
   node;
   return true;
end function;

IsRybaGroup := function (G)
   if Type(G) eq GrpMat and assigned G`Ryba then
      return G`Ryba eq true; 
   else 
      return false;
   end if;
end function;

UserWords := function (G)
   if Type(G) eq GrpMat and assigned G`UserWords then
      return G`UserWords;
   else 
      return false;
   end if;
end function;

IsSL2Group := function (G)
   if Type(G) eq GrpMat and assigned G`SL2Flag then
      return G`SL2Flag eq true; 
   else 
      return "unknown";
   end if;
end function;

IsRootNode := function (node)
   if assigned node`parent then
      return node`parent eq 0; 
   else 
      return false;
   end if;
   // return node`type eq "root";
end function;

IsRightChild := function (node, A)
   if not IsRootNode (node) and assigned A[ParentOfNode (node)]`right then 
      return A[ParentOfNode (node)]`right eq node`identifier;
   else 
      return false;
   end if;
end function;

IsLeftChild := function (node, A)
   if not IsRootNode (node) and assigned A[ParentOfNode (node)]`left then 
      return A[ParentOfNode (node)]`left eq node`identifier;
   else 
      return false;
   end if;
end function;

/* deassign all entries in the tree having node as ancestor */

procedure PruneTree (~A, node)

   /* discard all entries after A */
   A := [A[i]: i in [1..node`identifier]];
   for i in [1..#A] do
     if assigned A[i]`left and A[i]`left gt #A then
        delete A[i]`left;
     end if;
     if assigned A[i]`right and A[i]`right gt #A then
        delete A[i]`right;
     end if;
   end for;  
end procedure;

IsOnMainLine := function (node, A)

   if IsRootNode (node) then return true; end if;
   if IsLeftChild (node, A) then return false; end if;
   if IsRightChild (node, A) then 
      return $$ (A[ParentOfNode (node)], A); 
   end if;
   return "unknown"; 
end function;

HasChildren := function (node, A)
   if assigned A[node`identifier]`left and 
	 assigned A[node`identifier]`right then
      return true;
   else
      return false;
   end if;
end function;         

IsNodeProcessed := function (node, A)
   // "NODE is ", node`identifier;
   // "HAS CHILDREN? ", HasChildren (node, A);
   // "HERE ISLEAF ? ", IsLeaf (node);
   return HasChildren (node, A) or IsLeaf (node);
end function;

ReportTree := function (A)

    for i in [1..#A] do 
       G := A[i]`group;
       if assigned G`ActionType then
          "node ", i;
          "parent ", ParentOfNode (A[i]);
          // "parent ", G`parent;
          "action = ", G`ActionType;
          "--------------------------------";
       end if;
     end for;
     return true;
end function;

/* report submodule lattice */

ReportLattice := function (G, L)
   if Type (G) eq GrpMat then 
      d := Degree (G);
   else 
      d := Dimension (G);
   end if;
   F := BaseRing (G);
   V := VectorSpace (F, d);
   S := []; dim := [];
   for i in [1..#L] do 
      B := Morphism (L!i);
      Base := [V!B[i]: i in [1..Dimension(Domain(B))]];
      S[i] := sub <V | Base>;
      dim[i] := Dimension (S[i]);
   end for;
   return dim, S;
end function;

/* decide if disrete log computation is practical in Magma

   If the field characteristic is 2, then Magma uses the 
   fast Coppersmith algorithm which works pretty quickly 
   up to about GF(2^300).

   For GF(p^n) for small p > 2, Magma uses the Pollard-Rho
   algorithm.  This involves (very roughly) about S field operations, 
   where S = the square root of the largest prime dividing p^n - 1. */

CanApplyDiscreteLog := function (F: Limit := 10^7)
   q := #F; 
   flag, p, n := IsPrimePower (q);
   if p eq 2 and n le 300 then return true; end if;
   if p eq 2 and n gt 300 then return false; end if;
   if p gt 10 and n gt 50 then return false; end if;
   estimate := Isqrt (Maximum (PrimeBasis (p^n - 1)));
   return estimate lt Limit; 
end function;

/* set up hom from B -> G where U is the list of images of
   generators of B; do it in this way to  ensure that it
   does not force membership testing in G */

MyHom := function (G, B, U)
   d := Degree (G);
   F := BaseRing (G);
   gens := [GL (d, F) ! G.i : i in [1..Ngens (G)]];
   pos := [Position (gens, U[i]) : i in [1..#U]];
   return hom <B -> G | [G.i : i in pos]>;

end function;

TensorDimensions := function (G)
   fac := TensorFactors (G);
   u := Degree (Rep (fac[1]));
   w := Degree (Rep (fac[2]));
   return u, w;
end function;

