96,0
A,GrpMat,1,RandomProcess
V,UserUtil,5
S,RandomInvolution,Find an involution in G by random search.,0,1,0,0,0,0,0,178,,180,137,-38,-38,-38
S,RandomElementOfPseudoOrder,Find an element of the given pseudo-order G by random search. Also returns the order multiple.,0,2,0,0,0,0,0,148,,0,0,178,,180,137,148,-38,-38
S,RandomElementOfOrder,Find an element of the given order G by random search.,0,2,0,0,0,0,0,148,,0,0,178,,180,137,-38,-38,-38
S,IsMetabelian,One-sided Monte-Carlo check if G is metabelian. A negative answer is always correct. Error probability is at most 3/4.,0,1,0,0,0,0,0,178,,36,-38,-38,-38,-38
S,FrobeniusTwist,"Frobenius twist of a matrix M, ie take every element to power p^r",0,3,0,0,0,0,0,148,,0,0,148,,0,0,-34,,180,-38,-38,-38,-38
S,FrobeniusTwist,"Frobenius twist of a matrix group G, ie take FrobeniusTwist r of every generator",0,3,0,0,0,0,0,148,,0,0,148,,0,0,178,,178,175,-38,-38,-38
S,FrobeniusTwist,"Frobenius twist of a vector v, ie take every element to power p^r",0,3,0,0,0,0,0,148,,0,0,148,,0,0,160,,160,-38,-38,-38,-38
S,FrobeniusTwist,"Frobenius twist of a vector space V, ie take FrobeniusTwist r of every generator",0,3,0,0,0,0,0,148,,0,0,148,,0,0,159,,159,175,-38,-38,-38
S,DiagonaliseMatrix,Diagonalise M,0,1,0,0,0,0,0,-34,,-34,-34,-38,-38,-38
S,BrayAlgorithm,Bray Trick for computing involution centraliser in G of involution g,0,3,0,0,0,0,0,137,,0,0,180,,0,0,178,,178,82,-38,-38,-38
S,DihedralTrick,"Dihedral trick: if a^2 = b^2 = 1, and b * a = c has odd order 2n + 1, then c^-n * a * c^n = b if b * a does not have odd order, then choose random conjugate a^x of a such that b * a^x = c has odd order; now conjugate from a -> a^x -> b In our case, x and y should be MatSLP records, and the random conjugating elements are chosen from R.",0,3,0,0,0,0,0,106,,0,0,270,,0,0,270,,270,-38,-38,-38,-38
S,ScaleMatrix,Remove scalars from g,0,1,0,0,0,0,0,180,,180,-38,-38,-38,-38
S,ScaledTensorFactors,return tensor factors which have determinant 1,0,2,0,0,0,0,0,303,,0,0,178,,178,178,178,178,-38
