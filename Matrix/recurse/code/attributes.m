declare attributes GrpMat: RandomElements, Seed, NormalSeed, 
SLPGroup, SLPGroupHom, UserGenerators, UserWords, 
ChangeOfBasis, 
InverseWordMap, Submodule, ParentModule, 
CompositionFactors,
CompositionFactor,
ActionType, 
UnipotentDepth,
UnipotentImage, 
AbsoluteMap,
Basis,
ParentUnipotentImage,
CentraliserElements,
CentraliserTrees,
DeterminantImageMap,
SL2Basis,
SL2Flag, 
SL2Group,
Ryba,
CompSeries
;

declare attributes GrpPerm: RandomElements, Seed, NormalSeed, 
SLPGroup, SLPGroupHom, UserGenerators, UserWords, 
InverseWordMap, Basis, Submodule,
CentraliserTrees,
CompSeries,
ActionType; 

declare attributes GrpAb: RandomElements, Seed, NormalSeed, 
SLPGroup, SLPGroupHom, UserGenerators, Basis, MatrixGenerator, 
CentraliserTrees,
UserWords, InverseWordMap, ActionType; 

declare attributes GrpPC: UserGenerators, SLPGroup, SLPGroupHom, 
RandomElements, InverseWordMap, Submodule,
CentraliserTrees,
CompSeries,
ActionType; 

declare attributes GrpAb: UserGenerators, SLPGroup, SLPGroupHom, 
CompSeries,
RandomElements;

declare attributes GrpSLP: RandomProcess, Relations;

declare verbose sl2q, 2;

intrinsic UserGenerators (G :: GrpMat) -> SeqEnum
{Return supplied or defining generators of G, where scalar matrix is returned separately}
   if assigned G`UserGenerators then return G`UserGenerators; 
   else return [G.i: i in [1..Ngens (G)]]; end if;
end intrinsic;                                                                  
intrinsic UserGenerators (G :: GrpPC) -> SeqEnum
{Return supplied or defining generators of G}
   if assigned G`UserGenerators then return G`UserGenerators; 
   else return [G.i: i in [1..NPCgens (G)]]; end if;
end intrinsic;                                                                  
intrinsic UserGenerators (G :: GrpAb) -> SeqEnum
{Return supplied or defining generators of G}
   if assigned G`UserGenerators then return G`UserGenerators; 
   else return [G.i: i in [1..Ngens (G)]]; end if;
end intrinsic;                                                                  
