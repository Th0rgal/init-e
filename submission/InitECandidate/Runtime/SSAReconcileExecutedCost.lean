import InitECandidate.Runtime.AllocCostReconcile
import InitECandidate.Runtime.WordPermuteGlobalCost
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAReconcile

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 4000000

/-- Actual executed reconciliation work under the optimizer price, with no
extra charge for the syntactic Skip that represents an empty move list. -/
theorem ssaReconcile_optimizer_cost {C F β : Type} (cur target : Spt Nat) (names : Spt β)
    (state : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost wordOptimizerLocalPrice (ssaReconcile (width := 64) cur target names) state ≤
      24 * (sptToAList names).length := by
  have bound := ssaReconcile_length cur target names
  dsimp only at bound
  unfold ssaReconcile
  dsimp only
  split
  · simp only [wordExecutionCost, wordOptimizerLocalPrice,
      WordToStack.refinedWordLocalPrice, WordToStack.refinedWordStackLeafBudget]
    exact Nat.zero_le _
  · simp only [wordExecutionCost, wordOptimizerLocalPrice]
    have lengthEq : ((sptToAList names).map Prod.fst).length = (sptToAList names).length := List.length_map ..
    rw [lengthEq] at bound
    exact Nat.mul_le_mul_left 24 bound

/-- The original reconciliation theorem constructs the real run and memory
frame. Its executed move allowance is discharged here, rather than supplied
as an uninstantiated semantic or cost oracle. -/
theorem evaluateSSAReconcile_cost {C F β : Type}
    (next : Nat) (cur targetMap : Spt Nat) (names : Spt β)
    (sourceLocals : Spt (WordLocW 64)) (target : WordSemStateFiniteExact 64 C F)
    (related : ssaLocalsRel next cur sourceLocals target.locals)
    (injective : ∀ x y, sptDomain names x → sptDomain names y →
      optionLookup targetMap x = optionLookup targetMap y → x = y) :
    ∃ after, evaluate (ssaReconcile cur targetMap names) target = (none, after) ∧
      Flapjack.WordAlloc.wordStateEqRel target after ∧
      Flapjack.WordAlloc.strongLocalsRel (optionLookup targetMap) (sptDomain names)
        sourceLocals after.locals ∧
      wordExecutionCost wordOptimizerLocalPrice (ssaReconcile cur targetMap names) target ≤
        24 * (sptToAList names).length := by
  obtain ⟨after, run, frame, locals⟩ := evaluateSSAReconcile next cur targetMap names sourceLocals target
    ⟨related, injective⟩
  exact ⟨after, run, frame, locals, ssaReconcile_optimizer_cost cur targetMap names target⟩

/-- Adding a back-edge after an actual fall-through body pays its reached
move work. The compiler collapses an empty Skip back-edge. -/
theorem skip_collapsed_backedge_cost {C F : Type}
    (body moves : WordLangProgHOL (BitVec 64))
    (before after : WordSemStateFiniteExact 64 C F) (run : evaluate body before = (none, after)) :
    wordExecutionCost wordOptimizerLocalPrice (match moves with | .skip => body | _ => .seq body moves) before ≤
      wordExecutionCost wordOptimizerLocalPrice body before + wordExecutionCost wordOptimizerLocalPrice moves after := by
  cases moves
  all_goals first
    | exact Nat.le_add_right _ _
    | (rw [wordExecutionCost_seq, run]
       simp only [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
         WordToStack.refinedWordStackLeafBudget, Nat.zero_add, Nat.le_refl])

/-- Actual SSA fall-through body followed by the concrete emitted reconcile.
The output-map relation is consumed and a refreshed strong loop-head relation
is produced. No assertion relates arbitrary or independently chosen source
permutations: `source` is the particular post-body semantic witness. -/
theorem ssa_body_none_reconcile_cost {C F : Type}
    (source before after : WordSemStateFiniteExact 64 C F)
    (body : WordLangProgHOL (BitVec 64)) (mapOut refreshed : Spt Nat)
    (nextOut : Nat) (names : Spt Unit)
    (run : evaluate body before = (none, after))
    (frame : Flapjack.WordAlloc.wordStateEqRel source after)
    (locals : ssaLocalsRel nextOut mapOut source.locals after.locals)
    (injective : ∀ x y, sptDomain names x → sptDomain names y →
      optionLookup refreshed x = optionLookup refreshed y → x = y) :
    ∃ reconciled,
      evaluate (match ssaReconcile mapOut refreshed names with | .skip => body | moves => .seq body moves)
        before = (none, reconciled) ∧
      Flapjack.WordAlloc.wordStateEqRel source reconciled ∧
      Flapjack.WordAlloc.strongLocalsRel (optionLookup refreshed) (sptDomain names)
        source.locals reconciled.locals ∧
      wordExecutionCost wordOptimizerLocalPrice
        (match ssaReconcile mapOut refreshed names with | .skip => body | moves => .seq body moves) before ≤
        wordExecutionCost wordOptimizerLocalPrice body before + 24 * (sptToAList names).length := by
  obtain ⟨reconciled, reconcileRun, reconcileFrame, strong, cost⟩ :=
    evaluateSSAReconcile_cost nextOut mapOut refreshed names source.locals after locals injective
  refine ⟨reconciled, ?_, ?_, strong, ?_⟩
  · generalize movesEq : ssaReconcile (width := 64) mapOut refreshed names = moves at reconcileRun ⊢
    cases moves
    case skip =>
      have same : after = reconciled := by simpa only [evaluate] using congrArg Prod.snd reconcileRun
      simpa only [same] using run
    all_goals rw [evaluate, fix_clock_evaluate, run]
    all_goals exact reconcileRun
  · simp_all only [Flapjack.WordAlloc.wordStateEqRel, and_true]
  · have bound := (skip_collapsed_backedge_cost body (ssaReconcile mapOut refreshed names) before after run).trans
      (Nat.add_le_add_left cost _)
    generalize movesEq : ssaReconcile (width := 64) mapOut refreshed names = moves at bound ⊢
    cases moves <;> exact bound

#print axioms ssaReconcile_optimizer_cost
#print axioms evaluateSSAReconcile_cost
#print axioms skip_collapsed_backedge_cost
#print axioms ssa_body_none_reconcile_cost
end InitECandidate.Runtime.FineCost
