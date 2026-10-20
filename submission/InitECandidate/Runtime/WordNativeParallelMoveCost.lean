import InitECandidate.Runtime.WordNativeMoveCost
import InitECandidate.Runtime.ParallelMoveCost
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.Parmove

theorem native_move_aux_leaves {width : Nat} [NeZero width]
    (moves : List (Sum Nat Nat × Sum Nat Nat)) (kf : Nat × Nat × Nat) :
    stackLeaves (wMoveAuxNative (width := width) moves kf) ≤ 2 * moves.length + 1 := by
  induction moves with
  | nil => simp [wMoveAuxNative, stackLeaves]
  | cons pair rest ih =>
    have firstBound := native_single_move_leaves (width := width) pair kf
    cases rest with
    | nil => simpa only [wMoveAuxNative, List.length_cons, List.length_nil] using
        Nat.le_trans firstBound (by omega : 2 ≤ 2 * (0 + 1) + 1)
    | cons next tail =>
      simp only [wMoveAuxNative, stackLeaves, List.length_cons]
      simp only [List.length_cons] at ih
      omega

theorem native_move_aux_straight {width : Nat} [NeZero width]
    (moves : List (Sum Nat Nat × Sum Nat Nat)) (kf : Nat × Nat × Nat) :
    stackStraightLine (wMoveAuxNative (width := width) moves kf) = true := by
  induction moves with
  | nil => rfl
  | cons pair rest ih =>
    have first := native_single_move_straight (width := width) pair kf
    cases rest with
    | nil => exact first
    | cons next tail =>
      simp only [wMoveAuxNative, stackStraightLine, first, Bool.true_and]
      exact ih

/-- Parallel moves include cycle temporaries and stack-to-stack copies. -/
theorem native_parallel_move_leaves {width : Nat} [NeZero width]
    (moves : List (Nat × Nat)) (kf : Nat × Nat × Nat) :
    stackLeaves (wMoveNative (width := width) moves kf) ≤ 4 * moves.length + 1 := by
  let scheduled := parmove (moves.map (fun move => (move.1 / 2, move.2 / 2)))
  have scheduleBound : scheduled.length ≤ 2 * moves.length := by
    simpa only [scheduled, List.length_map] using
      parallel_move_length (moves.map (fun move => (move.1 / 2, move.2 / 2)))
  have lowered := native_move_aux_leaves (width := width)
    (scheduled.map (fun move =>
      (Compiler.Backend.WordToStackRegFormat.formatVar kf.1 move.1,
       Compiler.Backend.WordToStackRegFormat.formatVar kf.1 move.2))) kf
  simp only [List.length_map] at lowered
  dsimp only [scheduled] at lowered scheduleBound
  change stackLeaves (wMoveAuxNative _ kf) ≤ _
  omega

theorem native_parallel_move_straight {width : Nat} [NeZero width]
    (moves : List (Nat × Nat)) (kf : Nat × Nat × Nat) :
    stackStraightLine (wMoveNative (width := width) moves kf) = true := by
  exact native_move_aux_straight _ kf

#print axioms native_parallel_move_leaves
#print axioms native_parallel_move_straight
end InitECandidate.Runtime.FineCost
