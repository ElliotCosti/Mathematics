ImageOfTensorInducedElement := function (G, g)
   return TensorInducedAction (G, g);
end function;

TensorInducedImage := function (G)
   P := TensorInducedPermutations (G);
   n := Maximum ([Degree (x): x in P]);
   images := [TensorInducedAction (G, g):
               g in UserGenerators (G)];
   I := sub <Sym (n) | images>;
   I`UserGenerators := [I.j: j in [1..Ngens (G)]];
   return I, true;                       
end function;

ElementsActAsTensorInduced := function (G, TestElements)
   for g in TestElements do
      perm := TensorInducedAction (G, g);
      if Type (perm) eq BoolElt then return false; end if;
   end for;
   return true;
end function;                
