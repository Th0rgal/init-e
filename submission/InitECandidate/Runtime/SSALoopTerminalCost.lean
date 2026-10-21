import InitECandidate.Runtime.SSAQuantitativeCost
import InitECandidate.Runtime.SSALoopBackedgeExactCost

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 4000000

/-- A terminal body does not execute the appended reconciliation, including
when the compiler collapses an empty reconciliation to the body itself. -/
theorem ssa_body_terminal_reconcile {C F : Type}
    (TP : WordLangProgHOL (BitVec 64) → Nat)
    (seqZero : ∀ a b, TP (.seq a b) = 0)
    (body moves : WordLangProgHOL (BitVec 64))
    (before after : WordSemStateFiniteExact 64 C F) (result : WordSemResult 64)
    (run : evaluate body before = (some result, after)) :
    evaluate (match (generalizing := false) moves with | .skip => body | _ => .seq body moves) before =
        (some result, after) ∧
    wordExecutionCost (fun p _ => TP p)
        (match (generalizing := false) moves with | .skip => body | _ => .seq body moves) before =
      wordExecutionCost (fun p _ => TP p) body before := by
  cases moves
  case skip => exact ⟨run, rfl⟩
  all_goals dsimp only
  all_goals constructor
  all_goals first
    | (simp only [evaluate_def_rebound]; rw [run])
    | (rw [wordExecutionCost_seq, run, seqZero, Nat.zero_add]; rfl)

/-- Leaving the current loop shifts positive exit labels to the enclosing
SSA table. Terminal values keep their original locals equality. -/
theorem ssa_loop_terminal_locals {α : Type}
    (nextBody nextOut : Nat) (mapBody mapOut refreshed : Spt Nat)
    (names exits : Spt Unit) (tables : List (Spt Nat × Spt Unit × Spt Unit))
    (source target : Spt α) (result : Option (WordSemResult 64))
    (related : SSAResultLocals nextBody mapBody ((refreshed,names,exits)::tables)
      source target result)
    (terminal : wordSemContLoop result = false)
    (notExit : result ≠ some (.break 0)) :
    SSAResultLocals nextOut mapOut tables source target (wordSemExitLoop result) := by
  cases result with
  | none => simp [wordSemContLoop] at terminal
  | some value =>
    cases value with
    | «break» label =>
      cases label with
      | zero => exact False.elim (notExit rfl)
      | succ label => simpa [SSAResultLocals,wordSemExitLoop] using related
    | «continue» label =>
      cases label with
      | zero => simp [wordSemContLoop] at terminal
      | succ label => simpa [SSAResultLocals,wordSemExitLoop] using related
    | result value values => exact related
    | exception value payload => exact related
    | timeOut => exact related
    | notEnoughSpace => exact related
    | finalFfi event => exact related
    | error => exact related

/-- The non-recursive loop branch consumes the actual body runs and the
body induction bound. Reconciliation costs nothing here because it is not
executed. This includes positive exits, returns, exceptions and timeouts. -/
theorem ssa_loop_terminal_cost {C F : Type}
    (SP TP : WordLangProgHOL (BitVec 64) → Nat)
    (seqZero : ∀ a b, TP (.seq a b) = 0)
    (names exits targetNames targetExits : Spt Unit)
    (body output moves : WordLangProgHOL (BitVec 64))
    (source sourceEntry sourcePost target targetEntry targetPost : WordSemStateFiniteExact 64 C F)
    (result : WordSemResult 64)
    (sourceCut : cutState (names, .ln) source = some sourceEntry)
    (targetCut : cutState (targetNames, .ln) target = some targetEntry)
    (sourceRun : evaluate body sourceEntry = (some result, sourcePost))
    (targetRun : evaluate output targetEntry = (some result, targetPost))
    (terminal : wordSemContLoop (some result) = false)
    (notExit : (some result : Option (WordSemResult 64)) ≠ some (.break 0))
    (bodyCost : wordExecutionCost (fun p _ => TP p) output targetEntry ≤
      wordExecutionCost (fun p _ => SP p) body sourceEntry)
    (headCost : TP (.loop targetNames
      (match (generalizing := false) moves with | .skip => output | _ => .seq output moves) targetExits) ≤
      SP (.loop names body exits)) :
    let finalBody := match (generalizing := false) moves with | .skip => output | _ => .seq output moves
    evaluate (.loop names body exits) source = (wordSemExitLoop (some result), sourcePost) ∧
    evaluate (.loop targetNames finalBody targetExits) target =
      (wordSemExitLoop (some result), targetPost) ∧
    wordExecutionCost (fun p _ => TP p) (.loop targetNames finalBody targetExits) target ≤
      wordExecutionCost (fun p _ => SP p) (.loop names body exits) source := by
  dsimp only
  obtain ⟨finalRun, finalCost⟩ := ssa_body_terminal_reconcile TP seqZero output moves
    targetEntry targetPost result targetRun
  have sourceLoop := WordToWord.evaluate_loop_run names exits body source sourceEntry
    sourceCut (some result) sourcePost sourceRun
  have targetLoop := WordToWord.evaluate_loop_run targetNames targetExits
    (match (generalizing := false) moves with | .skip => output | _ => .seq output moves) target targetEntry
    targetCut (some result) targetPost finalRun
  have sourceCost := pure_loop_cost_run SP names exits body source sourceEntry sourcePost
    (some result) sourceCut sourceRun
  have targetCost := pure_loop_cost_run TP targetNames targetExits
    (match (generalizing := false) moves with | .skip => output | _ => .seq output moves) target targetEntry targetPost
    (some result) targetCut finalRun
  constructor
  · simpa only [terminal, Bool.false_eq_true, if_false, notExit] using sourceLoop
  constructor
  · simpa only [terminal, Bool.false_eq_true, if_false, notExit] using targetLoop
  · rw [sourceCost, targetCost, finalCost]
    simp only [terminal, Bool.false_eq_true, if_false, Nat.add_zero]
    exact Nat.add_le_add headCost bodyCost

#print axioms ssa_loop_terminal_cost
#print axioms ssa_body_terminal_reconcile
#print axioms ssa_loop_terminal_locals
end InitECandidate.Runtime.FineCost
