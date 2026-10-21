import InitECandidate.Runtime.WordStackExecutedLeaf
import InitECandidate.Runtime.ParmoveEmissionBound
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.MoveFull
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.WordToStackProofs
open Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open InitECandidate.Runtime.StackToLab

theorem wordStack_move_single_cost {F : Type} (move : Sum Nat Nat × Sum Nat Nat)
    (kf : Nat × Nat × Nat) (small : kf.2.1 ≤ 92)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (wMoveSingleNative move kf) source ≤ 14 := by
  rcases move with ⟨dst, src⟩
  have slot (register : Nat) : kf.2.1 - 1 - (register-kf.1) ≤ 91 := by omega
  cases dst with
  | inl dst =>
    cases src with
    | inl src => simp [wMoveSingleNative, stackExecutionCost, removalLocalPrice, nativePriceWithGap, instLocalCost]
    | inr src =>
      simp only [wMoveSingleNative, stackExecutionCost, guest_spill_load_price _ _ (slot src)]
      decide
  | inr dst =>
    cases src with
    | inl src =>
      simp only [wMoveSingleNative, stackExecutionCost, guest_spill_store_price _ _ (slot dst)]
      decide
    | inr src =>
      apply stackCost_seq_le (removalLocalPrice 6 riscvConfig.addrOffset) _ _ 7 7 rfl
        (fun s => ?_) (fun s => ?_) source
      · simp only [stackExecutionCost, guest_spill_load_price _ _ (slot src), Nat.le_refl]
      · simp only [stackExecutionCost, guest_spill_store_price _ _ (slot dst), Nat.le_refl]

theorem wordStack_move_aux_cost {F : Type} (moves : List (Sum Nat Nat × Sum Nat Nat))
    (kf : Nat × Nat × Nat) (small : kf.2.1 ≤ 92)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (wMoveAuxNative moves kf) source ≤ 14 * moves.length := by
  induction moves generalizing source with
  | nil => simp [wMoveAuxNative, stackExecutionCost, removalLocalPrice, nativePriceWithGap]
  | cons move rest ih =>
    cases rest with
    | nil => simpa only [wMoveAuxNative, List.length_singleton, Nat.mul_one] using
        wordStack_move_single_cost move kf small source
    | cons next tail =>
      have bound := stackCost_seq_le (removalLocalPrice 6 riscvConfig.addrOffset)
        (wMoveSingleNative move kf) (wMoveAuxNative (next::tail) kf)
        14 (14*(next::tail).length) rfl
        (fun s => wordStack_move_single_cost move kf small s) ih source
      simpa only [wMoveAuxNative, List.length_cons, Nat.mul_add, Nat.mul_one,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using bound

/-- The actual scheduler emits at most twice the source move count; each
emitted stack-to-stack move costs at most fourteen. -/
theorem wordStack_move_cost {F : Type} (moves : List (Nat × Nat))
    (kf : Nat × Nat × Nat) (small : kf.2.1 ≤ 92)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => removalLocalPrice 6 riscvConfig.addrOffset p)
      (wMoveNative moves kf) source ≤ 28 * moves.length := by
  unfold wMoveNative
  let scheduled := Parmove.parmove (moves.map (fun move => (move.1/2, move.2/2)))
  have bound := wordStack_move_aux_cost
    (scheduled.map (fun move => (WordToStackRegFormat.formatVar kf.1 move.1,
      WordToStackRegFormat.formatVar kf.1 move.2))) kf small source
  have emitted := parmove_length_le (moves.map (fun move => (move.1/2, move.2/2)))
  simp only [List.length_map] at bound emitted
  change scheduled.length ≤ 2*moves.length at emitted
  exact bound.trans (by omega)

theorem executedSimulation_move {F : Type} (ac : AsmConfigExact 64)
    (priority : Nat) (moves : List (Nat × Nat))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F) :
    ExecutedSimulation ac (.move priority moves) source (28 * moves.length) := by
  apply executedSimulation_of_fragment ac (.move priority moves) source (28*moves.length)
    (MoveFull.compCorrectMove ac priority moves source)
  intro k f frame bs n target small
  simp only [compNative]
  exact wordStack_move_cost moves (k,f,frame) small target

#print axioms wordStack_move_cost
#print axioms executedSimulation_move
end InitECandidate.Runtime.WordToStack
