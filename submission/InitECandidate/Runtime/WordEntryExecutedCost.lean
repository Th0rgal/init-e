import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCall
import InitECandidate.Runtime.WordRefinedLocalPrice
import InitECandidate.Runtime.WordStackHandlerRestoreCost
import Flapjack.Compiler.Backend.WordToStack.Proofs.SemanticsHelpers
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open InitECandidate.Runtime.FineCost InitECandidate.Runtime.StackToLab

/-- Actual compiled entry execution and cost, with the complete original
result/resource alternative. The target run is constructed, not assumed. -/
theorem compCall_refined_execution_cost {F : Type} (ac : AsmConfigExact 64)
    (start : Nat) (s : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (res : Option (WordSemResult 64)) (s1 : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (t : StackSemStateFiniteExact 64 LabToTarget.Config F) (lens : List Nat)
    (code : CostSupportedCode s.code) (frames : CodeFramesBounded s.code s.stackSize 92)
    (run : WordSemStateFiniteExact.evaluate (.call none (some start) [0] none) s = (res,s1))
    (notError : res ≠ some .error) (related : stateRel ac 22 0 0 s t lens 0) :
    ∃ (extra : Nat) (post : StackSemStateFiniteExact 64 LabToTarget.Config F)
      (output : Option (StackSemResult 64)),
      StackSemEvaluate.evaluate (.call none (.inl start) none,{t with clock := t.clock+extra}) = (output,post) ∧
      compCorrectResult ac 22 0 0 s s1 post res output lens ∧
      stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
        (.call none (.inl start) none) {t with clock := t.clock+extra} ≤
        wordExecutionCost refinedWordLocalPrice (.call none (some start) [0] none) s := by
  have simulation := refinedWordCost_correct ac (.call none (some start) [0] none) s rfl code frames
  obtain ⟨ck,t1,res1,targetRun,resultRel,cost⟩ :=
    simulation 22 0 0 s1 t res
      .nil .nil t.bitmaps.length t.bitmaps.length (.seq .skip (.call none (.inl start) none)) lens
      ⟨run, notError, related, by simp [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL, callArgConventionHOL, isPhyVar], by simp [flatExpConventions], by
        simp [compNative, callDestNative, seqStackFreeNative, Compiler.Backend.WordToStack.stackFree],
        by simp [appListAppend, appendAux], by simp [appListAppend, appendAux], by simp [appListAppend, appendAux],
        by simp [StackSem.getLabelsExact], by simp [maxVarHOL, maxList]⟩ (by decide)
  have callRun : StackSemEvaluate.evaluate (.call none (.inl start) none,
      {t with clock := t.clock+ck}) = (res1,t1) := (Flapjack.WordToStackProofs.CompCall.evaluateSeqSkip _ _).symm.trans targetRun
  have callCost := cost rfl
  rw [stackCost_seq_skip_left (price := refinedRemovalLocalPrice 6 riscvConfig.addrOffset)] at callCost
  exact ⟨ck,t1,res1,callRun,resultRel,callCost⟩

#print axioms compCall_refined_execution_cost
end InitECandidate.Runtime.WordToStack
