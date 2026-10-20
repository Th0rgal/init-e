import InitECandidate.Runtime.OriginalCreateBranchTwoLeavesCode
import InitECandidate.Runtime.MinCall
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def createBranchTwoLeavesLocals (k1 l1 v1 vl1 k2 l2 v2 vl2 : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64):=
 ((((((((HolFiniteMapExact.empty.update (ofString "k1",.val (.word k1))).update (ofString "l1",.val (.word l1))).update (ofString "v1",.val (.word v1))).update (ofString "vl1",.val (.word vl1))).update (ofString "k2",.val (.word k2))).update (ofString "l2",.val (.word l2))).update (ofString "v2",.val (.word v2))).update (ofString "vl2",.val (.word vl2)))

/-- Exact original eight-word branch-constructor call entry; bindings and
callee body follow from the installed original code, not an assumed call. -/
theorem create_branch_two_leaves_lookup {F : Type} (s : PanSemStateFiniteExact 64 F)
 (k1 l1 v1 vl1 k2 l2 v2 vl2 : BitVec 64) (code : s.code=originalRuntimeCode) :
 lookupCodeHOLFinite s.code.lookup (ofString "_create_branch_from_two_leaves")
  [.val (.word k1),.val (.word l1),.val (.word v1),.val (.word vl1),.val (.word k2),.val (.word l2),.val (.word v2),.val (.word vl2)]=
 some (sourceFunctionBody Guest.guestFn__create_branch_from_two_leaves,
  createBranchTwoLeavesLocals k1 l1 v1 vl1 k2 l2 v2 vl2,.one) := by
 apply lookupCodeFinite_of_exact
 rw [code]
 simp (config:={decide:=true}) [lookupCodeHOLExact,originalRuntimeCode_createBranchTwoLeaves_lookup,shapeOfHOLExact,shapeEqHOL]
 funext name
 by_cases h0 : name=ofString "vl2"
 · subst name;simp (config:={decide:=true}) [createBranchTwoLeavesLocals,HolFiniteMapExact.lookup_update,FUPDATE]
 · 
   by_cases h1 : name=ofString "v2"
   · subst name;simp (config:={decide:=true}) [createBranchTwoLeavesLocals,HolFiniteMapExact.lookup_update,FUPDATE]
   · 
     by_cases h2 : name=ofString "l2"
     · subst name;simp (config:={decide:=true}) [createBranchTwoLeavesLocals,HolFiniteMapExact.lookup_update,FUPDATE]
     · 
       by_cases h3 : name=ofString "k2"
       · subst name;simp (config:={decide:=true}) [createBranchTwoLeavesLocals,HolFiniteMapExact.lookup_update,FUPDATE]
       · 
         by_cases h4 : name=ofString "vl1"
         · subst name;simp (config:={decide:=true}) [createBranchTwoLeavesLocals,HolFiniteMapExact.lookup_update,FUPDATE]
         · 
           by_cases h5 : name=ofString "v1"
           · subst name;simp (config:={decide:=true}) [createBranchTwoLeavesLocals,HolFiniteMapExact.lookup_update,FUPDATE]
           · 
             by_cases h6 : name=ofString "l1"
             · subst name;simp (config:={decide:=true}) [createBranchTwoLeavesLocals,HolFiniteMapExact.lookup_update,FUPDATE]
             · 
               by_cases h7 : name=ofString "k1"
               · subst name;simp (config:={decide:=true}) [createBranchTwoLeavesLocals,HolFiniteMapExact.lookup_update,FUPDATE]
               · simp [createBranchTwoLeavesLocals,HolFiniteMapExact.lookup_update,FUPDATE,HolFiniteMapExact.empty,
                 h0,Ne.symm h0,h1,Ne.symm h1,h2,Ne.symm h2,h3,Ne.symm h3,h4,Ne.symm h4,h5,Ne.symm h5,h6,Ne.symm h6,h7,Ne.symm h7]

#print axioms create_branch_two_leaves_lookup
end InitECandidate.Runtime
