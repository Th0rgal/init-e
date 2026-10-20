import InitECandidate.Runtime.StackStraightLineCost
import Flapjack.Compiler.Backend.WordToStack.NativeInstructions
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordToStackRegFormat

/-- A spilled write adds exactly one frame store. -/
theorem native_write_leaves {width : Nat} [NeZero width]
    (g : Nat → HolProg width) (r : Nat) (kf : Nat × Nat × Nat)
    (bound : ∀ n, stackLeaves (g n) ≤ 1) :
    stackLeaves (wRegWrite1Native g r kf) ≤ 2 := by
  simp only [wRegWrite1Native]
  split
  · exact Nat.le_trans (bound _) (by omega)
  · simp only [stackLeaves]
    have := bound kf.1
    omega

theorem native_write_straight {width : Nat} [NeZero width]
    (g : Nat → HolProg width) (r : Nat) (kf : Nat × Nat × Nat)
    (supported : ∀ n, stackStraightLine (g n) = true) :
    stackStraightLine (wRegWrite1Native g r kf) = true := by
  simp only [wRegWrite1Native]
  split <;> simp [stackStraightLine, supported]

theorem native_load_leaves {width : Nat} [NeZero width]
    (loads : List (Nat × Nat)) (p : HolProg width) :
    stackLeaves (wStackLoadNative loads p) = loads.length + stackLeaves p := by
  induction loads with
  | nil => simp [wStackLoadNative]
  | cons pair rest ih =>
    rcases pair with ⟨r, slot⟩
    simp [wStackLoadNative, stackLeaves, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem native_load_straight {width : Nat} [NeZero width]
    (loads : List (Nat × Nat)) (p : HolProg width)
    (supported : stackStraightLine p = true) :
    stackStraightLine (wStackLoadNative loads p) = true := by
  induction loads with
  | nil => simpa [wStackLoadNative] using supported
  | cons pair rest ih =>
    rcases pair with ⟨r, slot⟩
    simp [wStackLoadNative, stackStraightLine, ih]

theorem first_register_load_count (r : Nat) (kf : Nat × Nat × Nat) :
    (wReg1 r kf).1.length ≤ 1 := by
  simp only [wReg1]
  split <;> simp

theorem second_register_load_count (r : Nat) (kf : Nat × Nat × Nat) :
    (wReg2 r kf).1.length ≤ 1 := by
  simp only [wReg2]
  split <;> simp

/-- Every integer instruction needs at most two reloads and one spilled write. -/
theorem native_instruction_leaves {width : Nat} [NeZero width]
    (instruction : Flapjack.Compiler.Encoders.Asm.HolInst width)
    (kf : Nat × Nat × Nat) : stackLeaves (wInstNative instruction kf) ≤ 4 := by
  cases instruction with
  | arith operation =>
    cases operation <;> try (rename_i op dst src operand; cases operand)
    all_goals simp only [wInstNative, native_load_leaves, List.length_append]
    all_goals first
      | (simp only [stackLeaves]; omega)
      | (apply Nat.le_trans (native_write_leaves _ _ kf (by intro n; rfl)); omega)
      | (apply Nat.le_trans (Nat.add_le_add (first_register_load_count _ kf)
          (native_write_leaves _ _ kf (by intro n; rfl))); omega)
      | (apply Nat.le_trans (Nat.add_le_add
          (Nat.add_le_add (first_register_load_count _ kf) (second_register_load_count _ kf))
          (native_write_leaves _ _ kf (by intro n; rfl))); omega)
      | (simp only [stackLeaves]
         apply Nat.le_trans (Nat.add_le_add_right (first_register_load_count _ kf) 1)
         omega)
      | (simp only [stackLeaves]
         apply Nat.le_trans (Nat.add_le_add_right
           (Nat.add_le_add (first_register_load_count _ kf) (second_register_load_count _ kf)) 1)
         omega)
  | mem operation dst address =>
    cases operation <;> cases address
    all_goals simp only [wInstNative, native_load_leaves, List.length_append]
    all_goals first
      | (simp only [stackLeaves]; omega)
      | (apply Nat.le_trans (native_write_leaves _ _ kf (by intro n; rfl)); omega)
      | (apply Nat.le_trans (Nat.add_le_add (first_register_load_count _ kf)
          (native_write_leaves _ _ kf (by intro n; rfl))); omega)
      | (apply Nat.le_trans (Nat.add_le_add
          (Nat.add_le_add (first_register_load_count _ kf) (second_register_load_count _ kf))
          (native_write_leaves _ _ kf (by intro n; rfl))); omega)
      | (simp only [stackLeaves]
         apply Nat.le_trans (Nat.add_le_add_right (first_register_load_count _ kf) 1)
         omega)
      | (simp only [stackLeaves]
         apply Nat.le_trans (Nat.add_le_add_right
           (Nat.add_le_add (first_register_load_count _ kf) (second_register_load_count _ kf)) 1)
         omega)
  | const dst value =>
    simp only [wInstNative]
    apply Nat.le_trans (native_write_leaves _ _ kf (by intro n; rfl))
    omega
  | _ => simp [wInstNative, stackLeaves]

theorem native_instruction_straight {width : Nat} [NeZero width]
    (instruction : Flapjack.Compiler.Encoders.Asm.HolInst width)
    (kf : Nat × Nat × Nat) : stackStraightLine (wInstNative instruction kf) = true := by
  cases instruction with
  | arith operation =>
    cases operation <;> try (rename_i op dst src operand; cases operand)
    all_goals simp only [wInstNative]
    all_goals first
      | rfl
      | exact native_load_straight _ _ (native_write_straight _ _ _ (by intro n; rfl))
      | exact native_load_straight _ _ rfl
  | mem operation dst address =>
    cases operation <;> cases address
    all_goals simp only [wInstNative]
    all_goals first
      | rfl
      | exact native_load_straight _ _ (native_write_straight _ _ _ (by intro n; rfl))
      | exact native_load_straight _ _ rfl
  | const dst value =>
    simp only [wInstNative]
    apply native_write_straight
    intro n
    rfl
  | _ => rfl

/-- Actual Stack-to-label path budget includes all reloads and spilled writes. -/
theorem native_instruction_path_bound {width : Nat} [NeZero width] {C F : Type}
    (instruction : Flapjack.Compiler.Encoders.Asm.HolInst width)
    (kf : Nat × Nat × Nat) (source : StackSemStateFiniteExact width C F) :
    StackToLab.pathWork (wInstNative instruction kf) source ≤ 14 := by
  have pathBound := stack_straight_path_bound (wInstNative instruction kf) source
    (native_instruction_straight instruction kf)
  have leavesBound := native_instruction_leaves instruction kf
  omega

#print axioms native_instruction_path_bound
#print axioms native_instruction_leaves

#print axioms native_load_leaves
end InitECandidate.Runtime.FineCost
