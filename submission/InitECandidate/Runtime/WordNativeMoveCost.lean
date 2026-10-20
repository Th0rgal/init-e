import InitECandidate.Runtime.WordNativeInstructionCost
import Flapjack.Compiler.Backend.WordToStack.NativeMoves
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.Parmove

/-- Scheduling a single move removes self-copies and introduces no temporary. -/
theorem singleton_parmove (destination source : Nat) :
    parmove [(destination, source)] =
      if source = destination then [] else [(some destination, some source)] := by
  simp only [parmove, List.map_cons, List.map_nil]
  rw [pmov]
  simp only [List.cons_ne_nil, false_and, ↓reduceDIte]
  simp only [fstep]
  by_cases same : source = destination
  · simp only [same, ↓reduceIte]
    rw [pmov]
    simp
  · simp only [Option.some.injEq, same, ↓reduceIte]
    rw [pmov]
    simp only [List.cons_ne_nil, and_false, ↓reduceDIte, fstep, splitSource]
    rw [pmov]
    simp

theorem native_single_move_leaves {width : Nat} [NeZero width]
    (pair : Sum Nat Nat × Sum Nat Nat) (kf : Nat × Nat × Nat) :
    stackLeaves (wMoveSingleNative (width := width) pair kf) ≤ 2 := by
  rcases pair with ⟨destination, source⟩
  cases destination <;> cases source <;> simp [wMoveSingleNative, stackLeaves]

theorem native_single_move_straight {width : Nat} [NeZero width]
    (pair : Sum Nat Nat × Sum Nat Nat) (kf : Nat × Nat × Nat) :
    stackStraightLine (wMoveSingleNative (width := width) pair kf) = true := by
  rcases pair with ⟨destination, source⟩
  cases destination <;> cases source <;> rfl

theorem native_singleton_move_leaves {width : Nat} [NeZero width]
    (destination source : Nat) (kf : Nat × Nat × Nat) :
    stackLeaves (wMoveNative (width := width) [(destination, source)] kf) ≤ 2 := by
  simp only [wMoveNative, List.map_cons, List.map_nil, singleton_parmove]
  split
  · simp [wMoveAuxNative, stackLeaves]
  · simp only [List.map_cons, List.map_nil, wMoveAuxNative]
    exact native_single_move_leaves _ kf

theorem native_singleton_move_straight {width : Nat} [NeZero width]
    (destination source : Nat) (kf : Nat × Nat × Nat) :
    stackStraightLine (wMoveNative (width := width) [(destination, source)] kf) = true := by
  simp only [wMoveNative, List.map_cons, List.map_nil, singleton_parmove]
  split
  · rfl
  · exact native_single_move_straight _ kf

#print axioms native_singleton_move_leaves
#print axioms native_singleton_move_straight
end InitECandidate.Runtime.FineCost
