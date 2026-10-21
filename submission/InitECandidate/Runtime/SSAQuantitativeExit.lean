import InitECandidate.Runtime.SSAQuantitativeCost
import Flapjack.Compiler.Backend.WordAlloc.Proofs.SSASemanticControl
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000
set_option pp.structureInstances false

/-- The two loop exits share the same reconciliation structure. -/
def ssaExitProgram (ongoing : Bool) (label : Nat) : WordLangProgHOL (BitVec 64) :=
  if ongoing then .continue label else .break label

/-- Exact static price of a skip-collapsed reconciliation and atomic exit. -/
def ssaReconcileExitPrice (price : WordLangProgHOL (BitVec 64) → Nat)
    (moves exit : WordLangProgHOL (BitVec 64)) : Nat :=
  match moves with
  | .skip => price exit
  | _ => price moves + price exit

def ssaExitLocalPrice (price : WordLangProgHOL (BitVec 64) → Nat)
    (ongoing : Bool) (label : Nat) (map : Spt Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit)) : Nat :=
  match tables[label]? with
  | none => price (ssaExitProgram ongoing label)
  | some (dest, entries, exits) =>
    ssaReconcileExitPrice price (ssaReconcile map dest (if ongoing then entries else exits))
      (ssaExitProgram ongoing label)

/-- Actual emitted reconciliation is a Skip or a single parallel move. Its
work before an atomic exit is bounded at those exact local prices, including
source-error short-circuiting of the move. No source/target run is assumed. -/
theorem ssa_reconcile_exit_cost {C F β : Type}
    (price : WordLangProgHOL (BitVec 64) → Nat) (seqZero : ∀ p q, price (.seq p q) = 0)
    (map dest : Spt Nat) (names : Spt β) (exit : WordLangProgHOL (BitVec 64))
    (atomic : wordCostAtomic exit = true) (target : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost (fun p _ => price p)
      (match ssaReconcile map dest names with | .skip => exit | moves => .seq moves exit) target ≤
      ssaReconcileExitPrice price (ssaReconcile map dest names) exit := by
  unfold ssaReconcile
  dsimp only
  split_ifs
  · exact Nat.le_of_eq (wordExecutionCost_atomic _ exit target atomic)
  · dsimp only [ssaReconcileExitPrice]
    rw [wordExecutionCost_seq]
    rw [seqZero, wordExecutionCost_atomic _ (.move _ _) _ rfl, Nat.zero_add]
    rcases run : evaluate (.move _ _) target with ⟨result, after⟩
    cases result with
    | none =>
      simp only
      rw [wordExecutionCost_atomic _ exit after atomic]
    | some result => simp only [Nat.add_zero]; exact Nat.le_add_right _ _

/-- Full quantitative Break/Continue SSA cases at exact emitted move prices.
The original semantic theorem supplies its actual permutation/result/frame/
exit-table relation. Atomic source cost is independent of that witness. -/
theorem ssa_quantitative_exit {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat) (ongoing : Bool) (label : Nat)
    (source target : WordSemStateFiniteExact 64 C F) (map : Spt Nat) (next : Nat)
    (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (seqZero : ∀ p q, TP (.seq p q) = 0)
    (localPrice : ssaExitLocalPrice TP ongoing label map tables ≤ SP (ssaExitProgram ongoing label))
    (h : Flapjack.WordAlloc.wordStateEqRel source target ∧
      ssaLocalsRel next map source.locals target.locals ∧ isAllocVar next ∧
      everyVarHOL (fun x => decide (x < next)) (ssaExitProgram ongoing label) = true ∧
      ssaMapOK next map ∧ ltOK tables) :
    SSAQuantitativeSimulation SP TP (ssaExitProgram ongoing label) source target map next tables := by
  have semantics : ssaSimulation (ssaExitProgram ongoing label) source target map next tables := by
    cases ongoing with
    | false => exact ssaCcTransCorrectBreak label source target map next tables h
    | true => exact ssaCcTransCorrectContinue label source target map next tables h
  have atomic : wordCostAtomic (ssaExitProgram ongoing label) = true := by cases ongoing <;> rfl
  have targetCost : wordExecutionCost (fun p _ => TP p)
      (ssaCcTrans (ssaExitProgram ongoing label) map next tables).1 target ≤
      ssaExitLocalPrice TP ongoing label map tables := by
    cases ongoing with
    | false =>
      cases selected : tables[label]? with
      | none => simp only [ssaExitProgram, Bool.false_eq_true, if_false, ssaCcTrans, selected, ssaExitLocalPrice,
          wordExecutionCost, Nat.le_refl]
      | some entry =>
        rcases entry with ⟨dest, entries, exits⟩
        have cost := ssa_reconcile_exit_cost TP seqZero map dest exits (.break label) rfl target
        generalize movesEq : ssaReconcile (width := 64) map dest exits = moves at cost ⊢
        cases moves <;> simpa only [ssaExitProgram, Bool.false_eq_true, if_false, ssaCcTrans, selected, ssaExitLocalPrice, movesEq] using cost
    | true =>
      cases selected : tables[label]? with
      | none => simp only [ssaExitProgram, if_true, ssaCcTrans, selected, ssaExitLocalPrice,
          wordExecutionCost, Nat.le_refl]
      | some entry =>
        rcases entry with ⟨dest, entries, exits⟩
        have cost := ssa_reconcile_exit_cost TP seqZero map dest entries (.continue label) rfl target
        generalize movesEq : ssaReconcile (width := 64) map dest entries = moves at cost ⊢
        cases moves <;> simpa only [ssaExitProgram, if_true, ssaCcTrans, selected, ssaExitLocalPrice, movesEq] using cost
  obtain ⟨permutation, post⟩ := ssa_semantic_witness (ssaExitProgram ongoing label) source target map next tables semantics
  refine ⟨permutation, ?_⟩
  rcases post with error | ⟨same, frame, locals⟩
  · exact Or.inl error
  · refine Or.inr ⟨same, frame, locals, ?_⟩
    rw [wordExecutionCost_atomic _ _ _ atomic]
    exact targetCost.trans localPrice

#print axioms ssa_reconcile_exit_cost
#print axioms ssa_quantitative_exit
end InitECandidate.Runtime.FineCost
