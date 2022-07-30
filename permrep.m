declare attributes GrpMat: PermRep, PermRepMap;

intrinsic PermutationRepresentation(G::GrpMat) -> GrpPerm
{A permutation group representation P of G, with homomorphism f: G -> P};
    // Only compute rep if not already stored.
    if not assigned G`PermRep then
        G`PermRepMap, G`PermRep := CosetAction(G, sub<G|>);
        123;
    end if;
    return G`PermRep, G`PermRepMap;
end intrinsic;
