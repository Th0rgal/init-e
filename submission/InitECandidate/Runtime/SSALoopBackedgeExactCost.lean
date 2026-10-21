import InitECandidate.Runtime.WordCseAtomicCost
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSAReconcile
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000
set_option pp.structureInstances false

/-- Reconciliation is always an atomic Skip or Move, with its real pair list. -/
theorem ssa_reconcile_atomic {β : Type} (map dest : Spt Nat) (names : Spt β) :
    wordCostAtomic (ssaReconcile (width := 64) map dest names) = true := by
  unfold ssaReconcile
  dsimp only
  split_ifs <;> rfl

/-- The pinned reconciliation constructs the actual run/frame/strong head
relation. Its work is exactly the supplied pure price of the emitted node. -/
theorem evaluateSSAReconcile_exact_cost {C F β : Type}
    (price : WordLangProgHOL (BitVec 64) → Nat)
    (next : Nat) (map dest : Spt Nat) (names : Spt β)
    (sourceLocals : Spt (WordLocW 64)) (target : WordSemStateFiniteExact 64 C F)
    (related : ssaLocalsRel next map sourceLocals target.locals)
    (injective : ∀ x y, sptDomain names x → sptDomain names y →
      optionLookup dest x = optionLookup dest y → x = y) :
    ∃ after, evaluate (ssaReconcile map dest names) target = (none, after) ∧
      Flapjack.WordAlloc.wordStateEqRel target after ∧
      Flapjack.WordAlloc.strongLocalsRel (optionLookup dest) (sptDomain names) sourceLocals after.locals ∧
      wordExecutionCost (fun p _ => price p) (ssaReconcile map dest names) target =
        price (ssaReconcile map dest names) := by
  obtain ⟨after, run, frame, strong⟩ := evaluateSSAReconcile next map dest names sourceLocals target
    ⟨related, injective⟩
  exact ⟨after, run, frame, strong, wordExecutionCost_atomic _ _ _ (ssa_reconcile_atomic map dest names)⟩

/-- Actual fall-through body followed by the emitted back-edge. The target's
strong refreshed loop-head relation is derived from the output-map SSA facts.
The only added work is the exact price of this one emitted reconciliation. -/
theorem ssa_body_none_reconcile_exact_cost {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → Nat) (seqZero : ∀ p q, price (.seq p q) = 0)
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
      wordExecutionCost (fun p _ => price p)
        (match ssaReconcile mapOut refreshed names with | .skip => body | moves => .seq body moves) before ≤
        wordExecutionCost (fun p _ => price p) body before + price (ssaReconcile mapOut refreshed names) := by
  obtain ⟨reconciled, reconcileRun, reconcileFrame, strong, cost⟩ :=
    evaluateSSAReconcile_exact_cost price nextOut mapOut refreshed names source.locals after locals injective
  refine ⟨reconciled, ?_, ?_, strong, ?_⟩
  · generalize movesEq : ssaReconcile (width := 64) mapOut refreshed names = moves at reconcileRun ⊢
    cases moves
    case skip =>
      have same : after = reconciled := by simpa only [evaluate] using congrArg Prod.snd reconcileRun
      simpa only [same] using run
    all_goals rw [evaluate, fix_clock_evaluate, run]
    all_goals exact reconcileRun
  · simp_all only [Flapjack.WordAlloc.wordStateEqRel, and_true]
  · generalize movesEq : ssaReconcile (width := 64) mapOut refreshed names = moves at reconcileRun cost ⊢
    cases moves
    case skip => exact Nat.le_add_right _ _
    all_goals rw [wordExecutionCost_seq, run]
    all_goals rw [seqZero, Nat.zero_add]
    all_goals dsimp only
    all_goals rw [← movesEq] at cost ⊢
    all_goals rw [cost]
    all_goals exact Nat.le_refl _

#print axioms ssa_reconcile_atomic
#print axioms evaluateSSAReconcile_exact_cost
#print axioms ssa_body_none_reconcile_exact_cost
end InitECandidate.Runtime.FineCost
