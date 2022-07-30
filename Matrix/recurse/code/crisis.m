/* add new generator g having definition gword to 
   node and update this node in A */

procedure AddNewGenerator (~A, node, g, gword)

   G := GroupOfNode (node);
   d := Degree (G);
   F := BaseRing (G);

   /* add in a new generator to node */
   U := UserGenerators (G);
   U := [GL(d, F) ! x : x in U];
   Append (~U, GL (d, F) ! g); 

   procedure CopyFields (G, ~H)
      if assigned G`Submodule then 
         H`ParentModule := G`ParentModule;
         H`Submodule := G`Submodule;
         H`ChangeOfBasis := G`ChangeOfBasis;
         H`ActionType := G`ActionType;
      end if;
   end procedure;

   H := sub <GL (d, F) | U >;
   H`UserGenerators := U;
   H`RandomElements := G`RandomElements;
   CopyFields (G, ~H);
   if not (gword cmpeq []) then 
      W := G`UserWords;
      Append (~W, gword); 
      H`UserWords := W;
   end if;
   B := SLPGroup (#H`UserGenerators);
   H`SLPGroup := B; 
   H`SLPGroupHom := MyHom (H, B, H`UserGenerators);
 
   vprint User1: "Number of new user generators is ", #H`UserGenerators;
   vprint User1: "Number of new generators is ", Ngens (H);
   node`group := H;
   A[node`identifier] := node;

end procedure;

procedure UpdateStoredInfo (~A, node)

   node := A[node`identifier];
   vprint User4: "After update order of node ", node`identifier, 
                 " is now ", #node`group, "\n";
   G := GroupOfNode (node);
   B := G`SLPGroup;

   /* words stored for kernel must be embedded as elements of 
      blackbox group B on larger number of generators */

   if not (LeftChildOfNode (node) cmpeq false) then
      left := A[LeftChildOfNode (node)];
      K := left`group;
      W := K`UserWords; 
      Original := Parent (Rep (W));
      incmap := hom <Original -> B | [B.i : i in [1..Ngens (Original)]]>;
      K`UserWords := [incmap (u): u in K`UserWords];
      left`group := K;
      A[left`identifier] := left;
   end if;

end procedure;

/* add g and gword to generating set for group defined 
   by node index of A */

procedure UpdateNode (~A, index, g, gword)

   node := A[index];
   G := GroupOfNode (node);

   vprint User2: "At entry number of generators is ", Ngens (G);
   node := A[index]; 

   AddNewGenerator (~A, node, g, gword);
   UpdateStoredInfo (~A, node);

end procedure;

/* we've discovered a problem at node w */

Crisis := function (w, A)

   if IsRootNode (w) then 
      "1 Unable to trigger crisis: element not in group?";
      return false, false;
   end if;

   if IsOnMainLine (w, A) then 
      vprint User1: "2 Unable to trigger crisis: element not in group?";
      return false, false;
      error "PROBLEM at MainLine in CRISIS"; 
   end if;

   PruneTree (~A, w);

   w := A[w`identifier];

   NmrTrials := 50;

   while (true) do 
      if IsRootNode (w) then 
         vprint User1: "3 Unable to trigger crisis: element not in group?";
          return false, false;
          break; end if;
      while IsRightChild (w, A) do 
         w := A[ParentOfNode (w)];
      end while;
      "Currently consider node w = ", w`identifier;
      vprint User2: "Currently consider node w = ", w`identifier;
      if IsRootNode (w) then 
         vprint User1: "4 Unable to trigger crisis: element not in group?";
          return false, false;
          break; end if;
    
      parent := A[ParentOfNode (w)];
      vprint User2: "Parent of w = ", parent`identifier;
      P := GroupOfNode (parent); 
      G := GroupOfNode (w); 
      RightChild := A[RightChildOfNode (parent)];

      NmrRandom := 0; update := 0; MaxUpdate := 5;
      while (NmrRandom lt NmrTrials) do 
         NmrRandom +:= 1;
         g, gword := RandomWord (P);

         image := ConstructImage (P, g);  
         flag, result := SolveWord (A, RightChild, image);

         "right flag value is ", flag;

         if flag cmpeq "unknown" then continue; end if;

         if flag cmpeq false then
            vprint User2: "Recursive call to Crisis -- earlier problem";
            PruneTree (~A, result);
            return $$ (A[result], A);
         end if;

         im, iword := EvaluateWord (P, result);
         k := g * im^-1;
         kword := gword * iword^-1;
         flag, result := SolveWord (A, w, k);

         // if flag cmpeq "unknown" then continue; end if;

         if flag cmpeq false or flag cmpeq "unknown" then 
            if flag cmpeq false and result lt w`identifier then 
               "2 Recursive call to Crisis -- earlier problem";
               PruneTree (~A, result);
               return $$ (A[result], A);
            end if;

            /* add in a new generator to node w */
            vprint User2: "Now UpdateNode node w = ", w`identifier;
            update +:= 1;
            PruneTree (~A, w);

if #UserGenerators (G) lt 30 then 
            UpdateNode (~A, w`identifier, k, kword);
/* 
"k in G?", k in G;
"ORDER OF PARENT is ", #P;
"ORDER OF G is ", #G;
for t in [1..#A] do
 t, #A[t]`group;
end for;
*/
            // if update ge MaxUpdate then 
               return A, w`identifier; 
//            end if;
         end if;
 
         NmrRandom +:= 1;
   else 
NmrRandom := NmrTrials + 1;
end if;

      end while;

      w := A[ParentOfNode (w)];

   end while;

   "4 Unable to trigger crisis: element not in group?";
   return false, false;
   error "Unable to trigger crisis";

end function;
