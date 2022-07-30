// g in node T[i]`group. Pull back to parent
PullBack := function (T, Ti, g)
   y, w := SolveWord(T, Ti, g);
   if not y then error "Element not in group"; end if;
   F := Parent (w); ng := Ngens(F);
   H := T[Ti`parent]`group;
   h := hom <F-> H | UserGenerators(H)>;
   return h(w);
end function;

forward PCGroupMatrixGroup;

PCGroupMatrixGroup := function(T,Ti)
// returns P, GtoP, PtoG, where GtoP, PtoG are inverse isomorphisms
  T1 := Ti; G := T1`group;
  if T1`type eq "leaf" then
     /* eob addition */
     if Type (G) eq GrpPC then 
        P := G;
        GtoP := IdentityHomomorphism (G);
     else
        P, GtoP := PCGroup(G);
     end if;

     if Category(G) eq GrpMat and (G`UserGenerators[1] ne Id(G)) then
       // factor out scalar
"HERE WE ARE";
       Q := sub< G | G`UserGenerators[1]>;
"NOW HERE WE ARE";
       P,Pms :=quo< P | Q @ GtoP >;
       GtoP := GtoP*Pms;
     end if;
     PtoG := hom< P->G | [ P.i @@ GtoP : i in [1..NPCgens(P)]] >;
     return P, GtoP, PtoG;
  end if;

  TR := T[T1`right]; GR := TR`group;
  TL := T[T1`left]; GL := TL`group;
print "Recursing right";
  PR, GRtoPR, PRtoGR := PCGroupMatrixGroup(T,TR); ngR := NPCgens(PR);
print "ngR=",ngR;
print "Recursing left";
  PL, GLtoPL, PLtoGL := PCGroupMatrixGroup(T,TL); ngL := NPCgens(PL);
print "ngL=",ngL;
  gensR := [ PullBack(T,TR,PR.i @ PRtoGR) : i in [1..ngR]];
  gensL := [ PL.i @ PLtoGL : i in [1..ngL]];
  // resulting presentation will be on generators gensR cat gensL

  FC := FreeGroup(ngR+ngL); // free group for result.
  FR := FPGroup(PR);
  FRtoFC := hom< FR->FC | [FC.i : i in [1..ngR]] >;
  PRtoFC := hom< PR->FC | [FC.i : i in [1..ngR]] : Check:=false  >;
  FL := FPGroup(PL);
  FLtoFC := hom< FL->FC | [FC.(ngR+j) : j in [1..ngL]] >;
  PLtoFC := hom< PL->FC | [FC.(ngR+j) : j in [1..ngL]] : Check:=false  >;
  // relsC will be relations of result - first relations of GL
  if ngL gt 0 then
    relsC := [ r @ FLtoFC : r in Relations(FL) ]; 
  else relsC :=[];
  end if;

  // next conjugation relations
  FRtoG := hom< FR->G | gensR >;
temp := hom< FC -> G |  gensR cat gensL >;
  if ngR gt 0 and ngL gt 0 then
    for i in [1..ngR] do for j in [1..ngL] do
      w := (gensL[j]^gensR[i]) @ GLtoPL @ PLtoFC;
      Append(~relsC,FC.(ngR+j)^FC.i = w );
if temp(FC.(ngR+j)^FC.i) ne temp(w) then print "BADC",i,j; end if;
    end for; end for;
  end if;
  
  //And finally relations of GR with tails in GL
  if ngR gt 0 then
    for r in Relations(FR) do
      if ngL gt 0 then
        w := (RHS(r)^-1 * LHS(r)) @ FRtoG @ GLtoPL @ PLtoFC;
      else w := Id(FC);
      end if;
      Append(~relsC, LHS(r) @ FRtoFC = (RHS(r) @ FRtoFC) * w);
if temp(LHS(r) @ FRtoFC) ne temp((RHS(r) @ FRtoFC) * w) then print "BAD",r; end if;
    end for;
  end if;

//print FC, relsC;
//print "Defining polycyclic";
   P, FCtoP := quo<GrpGPC: FC | relsC: Check := false >;
"7";
  
//print "Done";
"P is ", P;
"G is ", Type (G);
  PtoG := hom< P->G | gensR cat gensL >; 

"8";
  // GtoP is slightly trickier!
  PRtoG := hom< PR->G | gensR : Check:=false  >;
  GtoPfun := function(g)
    if ngR eq 0 then
      return  g @  GLtoPL @ PLtoFC @ FCtoP;
      //return  g @  GLtoPL @ PLtoFC @ FCtoFCQ @ FCQtoP;
    end if;
    gi := ConstructImage(G,g);
    if ngL eq 0 then
      return  gi @ GRtoPR @ PRtoFC @ FCtoP;
      //return  gi @ GRtoPR @ PRtoFC @ FCtoFCQ @ FCQtoP;
    end if;
    wr := gi @ GRtoPR @ PRtoFC;
    wl :=  ( (gi @ GRtoPR @ PRtoG)^-1 * g) @ GLtoPL @ PLtoFC;
    return (wr*wl) @ FCtoP;
    //return (wr*wl) @ FCtoFCQ @ FCQtoP;
  end function;

  GtoP := hom< G->P | g :-> GtoPfun(g) >;
  return P, GtoP, PtoG;
  
end function;
  
