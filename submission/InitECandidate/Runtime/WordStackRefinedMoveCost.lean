import InitECandidate.Runtime.WordStackSingletonMove
import InitECandidate.Runtime.WordStackRefinedSpillCost
import InitECandidate.Runtime.ParmoveEmissionBound
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCorrect.MoveFull
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.WordToStackProofs
open Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open InitECandidate.Runtime.StackToLab

theorem wordStack_move_single_refined_cost {F : Type} (move : Sum Nat Nat × Sum Nat Nat)
    (kf : Nat × Nat × Nat) (small : kf.2.1 ≤ 92)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
      (wMoveSingleNative move kf) source ≤ 12 := by
  rcases move with ⟨dst, src⟩
  have slot (register : Nat) : kf.2.1 - 1 - (register-kf.1) ≤ 91 := by omega
  cases dst with
  | inl dst =>
    cases src with
    | inl src => simp [wMoveSingleNative, stackExecutionCost, refinedRemovalLocalPrice, removalLocalPrice, refinedNativePriceWithGap, nativePriceWithGap, instLocalCost]
    | inr src =>
      simp only [wMoveSingleNative, stackExecutionCost, guest_spill_load_refined_price _ _ (slot src)]
      decide
  | inr dst =>
    cases src with
    | inl src =>
      simp only [wMoveSingleNative, stackExecutionCost, guest_spill_store_refined_price _ _ (slot dst)]
      decide
    | inr src =>
      apply stackCost_seq_le (refinedRemovalLocalPrice 6 riscvConfig.addrOffset) _ _ 6 6 rfl
        (fun s => ?_) (fun s => ?_) source
      · simp only [stackExecutionCost, guest_spill_load_refined_price _ _ (slot src), Nat.le_refl]
      · simp only [stackExecutionCost, guest_spill_store_refined_price _ _ (slot dst), Nat.le_refl]

theorem wordStack_move_aux_refined_cost {F : Type} (moves : List (Sum Nat Nat × Sum Nat Nat))
    (kf : Nat × Nat × Nat) (small : kf.2.1 ≤ 92)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
      (wMoveAuxNative moves kf) source ≤ 12 * moves.length := by
  induction moves generalizing source with
  | nil => simp [wMoveAuxNative, stackExecutionCost, refinedRemovalLocalPrice, removalLocalPrice, refinedNativePriceWithGap, nativePriceWithGap]
  | cons move rest ih =>
    cases rest with
    | nil => simpa only [wMoveAuxNative, List.length_singleton, Nat.mul_one] using
        wordStack_move_single_refined_cost move kf small source
    | cons next tail =>
      have bound := stackCost_seq_le (refinedRemovalLocalPrice 6 riscvConfig.addrOffset)
        (wMoveSingleNative move kf) (wMoveAuxNative (next::tail) kf)
        12 (12*(next::tail).length) rfl
        (fun s => wordStack_move_single_refined_cost move kf small s) ih source
      simpa only [wMoveAuxNative, List.length_cons, Nat.mul_add, Nat.mul_one,
        Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using bound

/-- The actual scheduler emits at most twice the source move count; each
emitted stack-to-stack move costs at most fourteen. -/
theorem wordStack_move_refined_cost {F : Type} (moves : List (Nat × Nat))
    (kf : Nat × Nat × Nat) (small : kf.2.1 ≤ 92)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
      (wMoveNative moves kf) source ≤ 24 * moves.length := by
  unfold wMoveNative
  let scheduled := Parmove.parmove (moves.map (fun move => (move.1/2, move.2/2)))
  have bound := wordStack_move_aux_refined_cost
    (scheduled.map (fun move => (WordToStackRegFormat.formatVar kf.1 move.1,
      WordToStackRegFormat.formatVar kf.1 move.2))) kf small source
  have emitted := parmove_length_le (moves.map (fun move => (move.1/2, move.2/2)))
  simp only [List.length_map] at bound emitted
  change scheduled.length ≤ 2*moves.length at emitted
  exact bound.trans (by omega)

/-- Singleton assignment needs no cycle-breaking scheduler overhead. -/
theorem wordStack_singleton_move_refined_cost {F : Type} (dst src : Nat)
    (kf : Nat × Nat × Nat) (small : kf.2.1 ≤ 92)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F) :
    stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
      (wMoveNative [(dst,src)] kf) source ≤ 12 := by
  simp only [wMoveNative, List.map_cons, List.map_nil, parmove_singleton]
  split
  · simp [wMoveAuxNative, stackExecutionCost, refinedRemovalLocalPrice, removalLocalPrice, refinedNativePriceWithGap, nativePriceWithGap]
  · simpa only [List.map_cons, List.map_nil, wMoveAuxNative] using
      wordStack_move_single_refined_cost
        (WordToStackRegFormat.formatVar kf.1 (some (dst/2)),
          WordToStackRegFormat.formatVar kf.1 (some (src/2))) kf small source

#print axioms wordStack_move_refined_cost
#print axioms wordStack_singleton_move_refined_cost
end InitECandidate.Runtime.WordToStack
