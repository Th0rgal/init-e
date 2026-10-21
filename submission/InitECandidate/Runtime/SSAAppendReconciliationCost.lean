import InitECandidate.Runtime.SSAReconciliationLineCost
import InitECandidate.Runtime.SSAReturningCostStitch
import InitECandidate.Runtime.SSAQuantitativeSeq
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSALoopSemanticHelpers
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000
set_option pp.structureInstances false

/-- Append actual reconciliation after a compiled branch. Its semantic
specification comes from the compiler's left/right fix-inconsistencies theorem;
its work comes from the exact emitted leaf sum. Terminal branches do not run
the moves. The source scheduler and source run are unchanged. -/
theorem ssa_append_reconciliation_cost {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → Nat) (seqZero : ∀ a b, price (.seq a b) = 0)
    (sourceRun : Option (WordSemResult 64) × WordSemStateFiniteExact 64 C F)
    (target : WordSemStateFiniteExact 64 C F)
    (compiled moves : WordLangProgHOL (BitVec 64))
    (mapOut finalMap : Spt Nat) (nextOut nextFinal : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit)) (sourceWork n : Nat)
    (line : lineBound (ssaReconciliationLeaf price) moves = some n)
    (moveSpec : ∀ (sourceAfter targetAfter : WordSemStateFiniteExact 64 C F),
      ssaLocalsRel nextOut mapOut sourceAfter.locals targetAfter.locals →
      let run := evaluate moves targetAfter
      run.1 = none ∧ ssaLocalsRel nextFinal finalMap sourceAfter.locals run.2.locals ∧
        Flapjack.WordAlloc.wordStateEqRel targetAfter run.2)
    (post : SSAQuantitativeOutcome mapOut nextOut tables sourceRun (evaluate compiled target)
      sourceWork (wordExecutionCost (fun p _ => price p) compiled target)) :
    SSAQuantitativeOutcome finalMap nextFinal tables sourceRun (evaluate (.seq compiled moves) target)
      (sourceWork + n) (wordExecutionCost (fun p _ => price p) (.seq compiled moves) target) := by
  rcases sourceRun with ⟨result, sourceAfter⟩
  rcases post with error | ⟨same, frame, locals, cost⟩
  · exact Or.inl error
  · rcases compiledRun : evaluate compiled target with ⟨targetResult, targetAfter⟩
    rw [compiledRun] at same frame locals
    have equal : targetResult = result := same.symm
    subst targetResult
    cases result with
    | none =>
      have moved := moveSpec sourceAfter targetAfter locals
      rcases moveRun : evaluate moves targetAfter with ⟨moveResult, moveAfter⟩
      rw [moveRun] at moved
      dsimp only at moved
      have equal : moveResult = none := moved.1
      subst moveResult
      right
      rw [evaluateSeqCollapse compiled moves target targetAfter compiledRun, moveRun]
      refine ⟨rfl, fakeMovesStateRelationTrans sourceAfter targetAfter moveAfter frame moved.2.2,
        moved.2.1, ?_⟩
      rw [wordExecutionCost_seq, compiledRun]
      simp only [seqZero, Nat.zero_add]
      exact Nat.add_le_add cost (ssa_reconciliation_line_cost price seqZero moves n line targetAfter)
    | some result =>
      right
      rw [evaluate, fix_clock_evaluate, compiledRun]
      refine ⟨rfl, frame, SSAResultLocals.terminal result locals, ?_⟩
      rw [wordExecutionCost_seq, compiledRun]
      simp only [seqZero, Nat.zero_add, Nat.add_zero]
      exact cost.trans (Nat.le_add_right sourceWork n)

#print axioms ssa_append_reconciliation_cost
end InitECandidate.Runtime.FineCost
