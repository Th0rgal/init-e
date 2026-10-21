import InitECandidate.Runtime.FullSSACodeTable
import InitECandidate.Runtime.WordCallExecutionCost
import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileSingleCorrect.Call
import Flapjack.Compiler.Backend.Semantics.WordSem.Props.NoInstallEvaluate
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000
set_option pp.structureInstances false

/-- The function simulation needed at a strictly smaller call clock. This is
an explicit induction interface, not an already established whole-table bound.
Both the changed code field and actual full SSA function entry are visible. -/
def FullSSATableFunctionAt {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat) (body : WordLangProgHOL (BitVec 64))
    (count : Nat) (entry : WordSemStateFiniteExact 64 C F) : Prop :=
  ∃ permutation : Nat → Nat → Nat,
    let sourceState := {entry with permute := permutation}
    let sourceRun := evaluate body sourceState
    let targetRun := evaluate (fullSsaCcTrans count body)
      {entry with code := fullSSACodeTable entry.code}
    sourceRun.1 = some .error ∨ sourceRun.1 = targetRun.1 ∧
      FullSSATableFrame sourceRun.2 targetRun.2 ∧
      (match sourceRun.1 with
      | none => True
      | some (.break _) => True
      | some (.continue _) => True
      | some _ => sourceRun.2.locals = targetRun.2.locals) ∧
      wordExecutionCost (fun p _ => TP p) (fullSsaCcTrans count body)
          {entry with code := fullSSACodeTable entry.code} ≤
        wordExecutionCost (fun p _ => SP p) body sourceState + fullSSAEntryPrice TP count body

def FullSSATableFunctionIH {C F : Type} (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (depth clock : Nat) : Prop :=
  ∀ (body : WordLangProgHOL (BitVec 64)) (count : Nat) (entry : WordSemStateFiniteExact 64 C F),
    Prod.Lex (· < ·) (· < ·) (entry.termdep,entry.clock) (depth,clock) →
    noInstallSubprogsHOL body = true → WordProps.noInstallCode entry.code →
    sptDomain entry.locals = (fun key => key ∈ evenList count) →
    (let setup := setupSSA (outputWidth := 64) count (limitVar body) body;
      ssaCostFits SP TP body setup.2.1 setup.2.2 []) →
    FullSSATableFunctionAt SP TP body count entry

/-- A tail call through the actual full-SSA table. The only callee execution
hypothesis is guarded by a strictly smaller clock/depth pair. Static funding
pays the real callee prologue/root setup; invalid source returns retain the
source-error exemption. This clause does not yet discharge the global IH. -/
theorem fullSSATable_tail_cost {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat) (prefixWork : Nat)
    (destination : Option Nat) (arguments targetArguments : List Nat)
    (source target : WordSemStateFiniteExact 64 C F)
    (frame : FullSSATableFrame source target)
    (argumentRead : ∀ inputs, getVars arguments source = some inputs → getVars targetArguments target = some inputs)
    (argumentGuard : wordSemBadDestArgs destination targetArguments = wordSemBadDestArgs destination arguments)
    (codeFree : WordProps.noInstallCode source.code)
    (fits : ∀ (inputs actualArguments : List (WordLocW 64)) (body : WordLangProgHOL (BitVec 64)) (size : Option Nat),
      wordSemFindCode destination inputs source.code source.stackSize = some (actualArguments,body,size) →
      let setup := setupSSA (outputWidth := 64) actualArguments.length (limitVar body) body;
      ssaCostFits SP TP body setup.2.1 setup.2.2 [])
    (funding : ∀ (inputs actualArguments : List (WordLocW 64)) (body : WordLangProgHOL (BitVec 64)) (size : Option Nat),
      wordSemFindCode destination inputs source.code source.stackSize = some (actualArguments,body,size) →
      prefixWork + TP (.call none destination targetArguments none) + fullSSAEntryPrice TP actualArguments.length body ≤
        SP (.call none destination arguments none))
    (ih : FullSSATableFunctionIH (C := C) (F := F) SP TP source.termdep source.clock) :
    ∃ permutation : Nat → Nat → Nat,
      let sourceState := {source with permute := permutation}
      let sourceRun := evaluate (.call none destination arguments none) sourceState
      let targetRun := evaluate (.call none destination targetArguments none) target
      sourceRun.1 = some .error ∨ sourceRun.1 = targetRun.1 ∧
        FullSSATableFrame sourceRun.2 targetRun.2 ∧ sourceRun.2.locals = targetRun.2.locals ∧
        prefixWork + wordExecutionCost (fun p _ => TP p) (.call none destination targetArguments none) target ≤
          wordExecutionCost (fun p _ => SP p) (.call none destination arguments none) sourceState := by
  classical
  have targetClock := (fullSSATableFrame_clock source target frame).1.symm
  have targetSizes : target.stackSize = source.stackSize := frame.1.2.2.2.2.2.2.1
  have targetCode := frame.2
  cases read : getVars arguments source with
  | none =>
    refine ⟨source.permute,Or.inl ?_⟩
    simp [WordToWord.evaluate_call_eq,read]
  | some inputs =>
    by_cases bad : wordSemBadDestArgs destination arguments = true
    · refine ⟨source.permute,Or.inl ?_⟩
      simp [WordToWord.evaluate_call_eq,read,bad]
    have good : wordSemBadDestArgs destination arguments = false := Bool.eq_false_iff.mpr bad
    cases found : wordSemFindCode destination inputs source.code source.stackSize with
    | none =>
      refine ⟨source.permute,Or.inl ?_⟩
      simp [WordToWord.evaluate_call_eq,read,good,wordSemAddRetLoc,found]
    | some triple =>
      obtain ⟨actualArguments,body,size⟩ := triple
      have targetRead : getVars targetArguments target = some inputs := argumentRead inputs read
      have targetGood : wordSemBadDestArgs destination targetArguments = false := argumentGuard.trans good
      have targetFound : wordSemFindCode destination inputs target.code target.stackSize =
          some (actualArguments,fullSsaCcTrans actualArguments.length body,size) := by
        rw [targetCode,
          targetSizes,fullSSACodeTable_findCode,found]
        rfl
      have localFunding := funding inputs actualArguments body size found
      by_cases zero : source.clock = 0
      · have sourceTimeout : evaluate (.call none destination arguments none) source =
            (some .timeOut,flushState true source) := by
          rw [WordToWord.evaluate_call_eq,read]
          simp only [good,Bool.false_eq_true,if_false,wordSemAddRetLoc,found,zero,if_true]
        have targetTimeout : evaluate (.call none destination targetArguments none) target =
            (some .timeOut,flushState true target) := by
          rw [WordToWord.evaluate_call_eq,targetRead]
          simp only [targetGood,Bool.false_eq_true,if_false,wordSemAddRetLoc,targetFound,
            targetClock,zero,if_true]
        refine ⟨source.permute,Or.inr ?_⟩
        change (evaluate (.call none destination arguments none) source).1 =
            (evaluate (.call none destination targetArguments none) target).1 ∧
          FullSSATableFrame (evaluate (.call none destination arguments none) source).2
            (evaluate (.call none destination targetArguments none) target).2 ∧
          (evaluate (.call none destination arguments none) source).2.locals =
            (evaluate (.call none destination targetArguments none) target).2.locals ∧
          prefixWork + wordExecutionCost (fun p _ => TP p) (.call none destination targetArguments none) target ≤
            wordExecutionCost (fun p _ => SP p) (.call none destination arguments none) source
        simp only [sourceTimeout,targetTimeout]
        refine ⟨trivial,?_,rfl,?_⟩
        · exact fullSSATableFrame_flush source target frame
        · rw [wordExecutionCost,wordExecutionCost]
          simp only [read,targetRead,good,targetGood,Bool.false_eq_true,if_false,wordSemAddRetLoc,
            found,targetFound,targetClock,zero,dif_pos rfl,dif_pos True.intro]
          omega
      · let base := {decClock source with permute := target.permute}
        let entry := callEnv actualArguments size base
        have smaller : Prod.Lex (· < ·) (· < ·) (entry.termdep,entry.clock) (source.termdep,source.clock) := by
          simp only [entry,base,WordSemStateFiniteExact.callEnv,decClock]
          apply Prod.Lex.right
          omega
        have bodyFree := WordProps.noInstallFindCode source.code destination inputs source.stackSize
          actualArguments body size ⟨codeFree,found⟩
        have bodyFits := fits inputs actualArguments body size found
        obtain ⟨permutation,post⟩ := ih body actualArguments.length entry smaller bodyFree codeFree
          (sptDomainFromList2 actualArguments) bodyFits
        let sourceState := {source with permute := permutation}
        have sourceRead : getVars arguments sourceState = some inputs := by
          rw [getVars_withPermute]
          exact read
        have sourceEntry : callEnv actualArguments size (decClock sourceState) =
            {entry with permute := permutation} := rfl
        have targetEntry : callEnv actualArguments size (decClock target) =
            {entry with code := fullSSACodeTable entry.code} := by
          have actual := fullSSATableFrame_callEnv (decClock source) (decClock target)
            (fullSSATableFrame_decClock source target frame) actualArguments size
          simpa only [entry,base,WordSemStateFiniteExact.callEnv,decClock] using actual
        rcases sourceCallee : evaluate body {entry with permute := permutation} with ⟨result,returned⟩
        dsimp only at post
        rw [sourceCallee] at post
        dsimp only at post
        have sourceRun : evaluate (.call none destination arguments none) sourceState =
            (if wordSemBadFunReturn result then (some .error,returned) else (result,returned)) := by
          rw [WordToWord.evaluate_call_eq,sourceRead]
          simp only [good,Bool.false_eq_true,if_false,wordSemAddRetLoc,
            show sourceState.code = source.code from rfl,show sourceState.stackSize = source.stackSize from rfl,
            found,show sourceState.clock = source.clock from rfl,zero,if_false,sourceEntry,sourceCallee]
        refine ⟨permutation,?_⟩
        dsimp only
        change _ ∨ _
        rw [sourceRun]
        rcases post with error | ⟨same,frame,locals,cost⟩
        · subst result
          exact Or.inl (by simp [wordSemBadFunReturn])
        · by_cases invalid : wordSemBadFunReturn result = true
          · exact Or.inl (by simp [invalid])
          have valid : wordSemBadFunReturn result = false := Bool.eq_false_iff.mpr invalid
          let targetReturned := (evaluate (fullSsaCcTrans actualArguments.length body)
            {entry with code := fullSSACodeTable entry.code}).2
          have targetCallee : evaluate (fullSsaCcTrans actualArguments.length body)
              (callEnv actualArguments size (decClock target)) = (result,targetReturned) := by
            rw [targetEntry]
            exact Prod.ext same.symm rfl
          have targetRun : evaluate (.call none destination targetArguments none) target = (result,targetReturned) := by
            rw [WordToWord.evaluate_call_eq,targetRead]
            simp only [targetGood,Bool.false_eq_true,if_false,wordSemAddRetLoc,targetFound,
              targetClock,zero,if_false,targetCallee,valid]
          rw [if_neg invalid,targetRun]
          right
          refine ⟨rfl,frame,?_,?_⟩
          · cases result with
            | none => simp [wordSemBadFunReturn] at valid
            | some outcome =>
              cases outcome <;> simp only [wordSemBadFunReturn] at valid
              all_goals first | contradiction | exact locals
          · rw [tail_call_cost _ destination targetArguments target inputs targetRead targetGood actualArguments
                (fullSsaCcTrans actualArguments.length body) size targetFound (by rw [targetClock]; exact zero),
              tail_call_cost _ destination arguments sourceState inputs sourceRead good actualArguments
                body size found zero,sourceEntry,targetEntry]
            dsimp only [entry,base] at cost ⊢
            omega

#print axioms fullSSATable_tail_cost
end InitECandidate.Runtime.FineCost
