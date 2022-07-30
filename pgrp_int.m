/*
Attach("C:/Documents and Settings/Elliot Costi/My Documents/Mathematics/pgrp_int.m");

*/

function Support(V, P)
    return sub<V | {v - v * p : v in Basis(V), p in Generators(P)}>;
end function;

intrinsic pGroupFlag(P :: GrpMat) -> []
    {}
    
    V := VectorSpace(P);
    supports := [];
    VP := V;

    // A theorem says VP < V, so loop will terminate
    repeat
	Append(~supports, VP);	
	VP := Support(VP, P);
    until Dimension(VP) eq 0;

    return supports;
end intrinsic;

intrinsic pGroupBasis(P :: GrpMat) -> GrpMatElt
    {P is a p-subgroup of GL(d, q) where q = p^e. 
     Return a change-of-basis matrix g in GL(d, q) such 
     that P^g is lower unitriangular.
    }
    local supports, V, VP, basis, U, W, conj;
    
    V := VectorSpace(P);
    F := BaseRing (P);
    p := Characteristic (F);

    if exists{x : x in Generators (P) | IsPowerOf (Order(x), p) eq false} then
       error "Input group is not a", p,"-group";
    end if;

    supports := pGroupFlag(P);
    
    basis := [];
    for i in Reverse([1 .. #supports]) do
	U := supports[i];
	W := sub<V | basis>;

	// Add basis elements from subspace
	for v in Basis(U) do
	    if v notin sub<V | W, basis> then
		Append(~basis, V ! v);
	    end if;
	end for;
    end for;

    conj := Generic(P) ! Matrix(F, Degree(P), Degree(P), basis);
    return conj^(-1);
end intrinsic;


// is i an index for a diagonal element when using LowerTriangularMatrix?
function isOnDiag(i, d)
    return i in {&+[j : j in [1 .. k]] : k in [1 .. d]};
end function;

intrinsic testIntersection(d :: RngIntElt, p :: RngIntElt,
    e :: RngIntElt) -> BoolElt
    { }

    F := GF(p, e);

    // Get p-groups
    G := sub<GL(d, F) | LowerTriangularMatrix([isOnDiag(i, d)
	select 1 else Random(F) : i in [1 .. d * (d + 1) div 2]])>;
    H := sub<GL(d, F) | LowerTriangularMatrix([isOnDiag(i, d) select 1
	else Random(F) : i in [1 .. d * (d + 1) div 2]])>;

    // Find preserved flag
    flag := pGroupFlag(G);

    // Replace other p-group with flag stabiliser
    S := H;
    for i in Reverse([2 .. #flag]) do
	S := UnipotentStabiliser(S, flag[i]);
    end for;

    // Write as upper and lower triangular matrices
    cbmL := pGroupBasis(G);
    cbmU := Generic(G) ! Reverse(RowSequence(cbmL));
    print G^cbmL, S^cbmU;
    
    return true;
end intrinsic;
