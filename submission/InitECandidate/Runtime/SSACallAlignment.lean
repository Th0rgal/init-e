import InitECandidate.Runtime.SSALoopSetupExecutedCost
import Flapjack.Compiler.Backend.WordAlloc.SSACcTrans
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticCallReturn

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.WordAlloc Flapjack.WordSemStateFiniteExact

/-! Reusable actual call-shape and popped-frame alignment facts, retained
from the obsolete control-node counter development. Executed-cost proofs now
use `wordExecutionCost`; one parallel move is not a unit-cost operation. -/

theorem ssaCcTrans_call_returning_none_output
    (ret : List Nat) (numset : Spt Unit × Spt Unit)
    (retHandler : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (ssa : Spt Nat) (na : Nat) (tables : List (Spt Nat × Spt Unit × Spt Unit)) :
    ssaCcTrans (width := 64) (.call (some (ret, numset, retHandler, l1, l2)) dest args none)
        ssa na tables =
      (let allNames := sptUnion numset.1 numset.2
       let ls := (sptToAList allNames).map Prod.fst
       let (stackMov, ssa', na') := listNextVarRenameMove (width := 64) ssa (na + 2) ls
       let stackSet := Flapjack.WordAlloc.applyNummapsKey (optionLookup ssa') numset
       let names := args.map (optionLookup ssa)
       let convArgs := (List.range names.length).map fun x => 2 * (x + 1)
       let moveArgs := WordLangProgHOL.move 1 (convArgs.zip names)
       let ssaCut := sptInter ssa' allNames
       let (retMov, ssa'', na'') := listNextVarRenameMove (width := 64) ssaCut (na' + 2) ls
       let (ret', ssa2p, na2p) := listNextVarRename ret ssa'' na''
       let (renRetHandler, ssa2, na2) := ssaCcTrans retHandler ssa2p na2p tables
       let regs := (List.range ret.length).map fun x => 2 * (x + 1)
       let movRetHandler := WordLangProgHOL.seq retMov
         (.seq (.move 1 (ret'.zip regs)) renRetHandler)
       (WordLangProgHOL.seq stackMov (.seq moveArgs
          (.call (some (regs, stackSet, movRetHandler, l1, l2)) dest convArgs none)),
        ssa2, na2)) := by
  simp only [ssaCcTrans]

theorem wordSemBadDestArgs_renameArgs {dest : Option Nat} {args args' : List Nat}
    (h : args = [] ↔ args' = []) :
    wordSemBadDestArgs dest args = wordSemBadDestArgs dest args' := by
  simp only [wordSemBadDestArgs]
  by_cases hd : dest = none
  · by_cases ha : args' = []
    · have ha' : args = [] := h.mpr ha
      simp only [hd, ha, ha']
    · have ha' : args ≠ [] := fun hc => ha (h.mp hc)
      simp only [hd, ha, ha']
  · simp only [hd, false_and]

theorem sourceCall_getVars_some_of_not_error {C F : Type}
    (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) (res : WordSemResult 64)
    (s' : WordSemStateFiniteExact 64 C F)
    (run : evaluate (.call ret dest args handler) s = (some res, s'))
    (hres : res ≠ .error) :
    ∃ xs, getVars args s = some xs := by
  rcases hg : getVars args s with _ | xs
  · have hcall : evaluate (.call ret dest args handler) s = (some .error, s) := by
      simp only [evaluate, hg]
    rw [hcall] at run
    simp only [Prod.mk.injEq, Option.some.injEq] at run
    exact absurd run.1.symm hres
  · exact ⟨xs, rfl⟩

theorem ssaCallReturning_pop_alignment {C F : Type}
    (source target returned : WordSemStateFiniteExact 64 C F)
    (first second targetFirst targetSecond : Spt (WordLocW 64))
    (handler targetHandler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (targetStack : List (WordSemStackFrame 64)) (f : Nat → Nat)
    (sourceRoots targetRoots : List (Nat × WordLocW 64))
    (sourcePerm targetPerm : Nat → Nat → Nat) (popped : WordSemStateFiniteExact 64 C F)
    (sourcePop : popEnv returned = some popped)
    (sameStack : source.stack = target.stack)
    (sourceRootRead : wordSemEnvToList second source.permute = (sourceRoots, sourcePerm))
    (targetRootRead : wordSemEnvToList targetSecond target.permute = (targetRoots, targetPerm))
    (rootMap : sourceRoots.map (fun (key, value) => (f key, value)) = targetRoots)
    (firstRelated : Flapjack.WordAlloc.strongLocalsRel f (sptDomain first) first targetFirst)
    (injective : ∀ a b, (sptDomain first a ∨ sptDomain second a) →
      (sptDomain first b ∨ sptDomain second b) → f a = f b → a = b)
    (sourceKeys : WordSemStackEq.sKeyEq
      (pushEnv (first, second) handler source).stack returned.stack)
    (targetKeys : WordSemStackEq.sKeyEq
      (pushEnv (targetFirst, targetSecond) targetHandler target).stack targetStack)
    (stackValues : WordSemStackEq.sValEq returned.stack targetStack) :
    ∃ targetPopped : WordSemStateFiniteExact 64 C F,
      popEnv {returned with stack := targetStack} = some targetPopped ∧
      Flapjack.WordAlloc.wordStateEqRel popped targetPopped ∧
      (∀ live, Flapjack.WordAlloc.strongLocalsRel f live popped.locals targetPopped.locals) := by
  obtain ⟨popped', targetPopped, hpop, hpopT, hframe, -, hrelated⟩ :=
    returningPopCutRelation source target returned first second targetFirst
      targetSecond handler targetHandler targetStack f sourceRoots targetRoots sourcePerm
      targetPerm sameStack sourceRootRead targetRootRead rootMap firstRelated injective
      sourceKeys targetKeys stackValues
  rw [sourcePop] at hpop
  have hEq : popped = popped' := by simpa using hpop
  subst hEq
  exact ⟨targetPopped, hpopT, hframe, hrelated⟩

#print axioms ssaCcTrans_call_returning_none_output
#print axioms wordSemBadDestArgs_renameArgs
#print axioms sourceCall_getVars_some_of_not_error
#print axioms ssaCallReturning_pop_alignment
end InitECandidate.Runtime.FineCost
