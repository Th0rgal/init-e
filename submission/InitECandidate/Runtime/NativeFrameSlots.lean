import InitECandidate.Runtime.GuestFrameCost
import InitECandidate.Runtime.AllocatedNativeCost
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordToStackRegFormat
open Flapjack.Compiler.Encoders.RiscV.Target

/-- Bounds only actual frame-relative accesses, not ordinary memory addresses. -/
def stackSlotsWithin {width : Nat} [NeZero width] (frame : Nat) : HolProg width → Bool
  | .stackLoad _ slot | .stackStore _ slot => decide (slot ≤ frame)
  | .seq first second => stackSlotsWithin frame first && stackSlotsWithin frame second
  | _ => true

theorem direct_removal_units (frame : Nat) (small : frame ≤ 92) (p : HolProg 64)
    (supported : stackStraightLine p = true) (within : stackSlotsWithin frame p = true) :
    stackRemovalUnits riscvConfig.addrOffset p = stackLeaves p := by
  cases p <;> simp only [stackStraightLine, Bool.and_eq_true] at supported
  all_goals try contradiction
  all_goals try rfl
  case stackLoad register slot =>
    simp only [stackSlotsWithin, decide_eq_true_eq] at within
    simp only [stackRemovalUnits, stackLeaves,
      small_frame_slot_direct slot (Nat.le_trans within small), ↓reduceIte]
  case stackStore register slot =>
    simp only [stackSlotsWithin, decide_eq_true_eq] at within
    simp only [stackRemovalUnits, stackLeaves,
      small_frame_slot_direct slot (Nat.le_trans within small), ↓reduceIte]
  case seq first second =>
    simp only [stackSlotsWithin, Bool.and_eq_true] at within
    have one := direct_removal_units frame small first supported.1 within.1
    have two := direct_removal_units frame small second supported.2 within.2
    simp only [stackRemovalUnits, stackLeaves, one, two]
termination_by sizeOf p

theorem native_write_slots {width : Nat} [NeZero width]
    (g : Nat → HolProg width) (r : Nat) (kf : Nat × Nat × Nat)
    (bounded : ∀ n, stackSlotsWithin kf.2.1 (g n) = true) :
    stackSlotsWithin kf.2.1 (wRegWrite1Native g r kf) = true := by
  simp only [wRegWrite1Native]
  split
  · exact bounded _
  · simp only [stackSlotsWithin, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨bounded _, by omega⟩

theorem native_load_slots {width : Nat} [NeZero width]
    (loads : List (Nat × Nat)) (p : HolProg width) (frame : Nat)
    (bounded : loads.all (fun entry => decide (entry.2 ≤ frame)) = true)
    (body : stackSlotsWithin frame p = true) :
    stackSlotsWithin frame (wStackLoadNative loads p) = true := by
  induction loads with
  | nil => exact body
  | cons pair rest ih =>
    rcases pair with ⟨register, slot⟩
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at bounded
    simp only [wStackLoadNative, stackSlotsWithin, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨bounded.1, ih bounded.2⟩

theorem first_register_slots (r : Nat) (kf : Nat × Nat × Nat) :
    (wReg1 r kf).1.all (fun entry => decide (entry.2 ≤ kf.2.1)) = true := by
  simp only [wReg1]
  split
  · rfl
  · simp only [List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq]
    omega

theorem second_register_slots (r : Nat) (kf : Nat × Nat × Nat) :
    (wReg2 r kf).1.all (fun entry => decide (entry.2 ≤ kf.2.1)) = true := by
  simp only [wReg2]
  split
  · rfl
  · simp only [List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq]
    omega

/-- Instruction reloads and spilled writes stay within the literal frame. -/
theorem native_instruction_slots {width : Nat} [NeZero width]
    (instruction : Compiler.Encoders.Asm.HolInst width) (kf : Nat × Nat × Nat) :
    stackSlotsWithin kf.2.1 (wInstNative instruction kf) = true := by
  cases instruction with
  | const destination value =>
    simp only [wInstNative]
    apply native_write_slots
    intro n
    rfl
  | arith operation =>
    cases operation <;> try (rename_i op destination src right; cases right)
    all_goals simp only [wInstNative]
    all_goals first
      | rfl
      | (apply native_load_slots
         · first
             | exact first_register_slots _ kf
             | simp only [List.all_append, first_register_slots, second_register_slots, Bool.true_and]
         · first
             | rfl
             | (apply native_write_slots; intro n; rfl))
  | mem operation destination address =>
    cases operation <;> cases address
    all_goals simp only [wInstNative]
    all_goals first
      | rfl
      | (apply native_load_slots
         · first
             | exact first_register_slots _ kf
             | simp only [List.all_append, first_register_slots, second_register_slots, Bool.true_and]
         · first
             | rfl
             | (apply native_write_slots; intro n; rfl))
  | _ => rfl

theorem native_single_move_slots {width : Nat} [NeZero width]
    (pair : Sum Nat Nat × Sum Nat Nat) (kf : Nat × Nat × Nat) :
    stackSlotsWithin kf.2.1 (wMoveSingleNative (width := width) pair kf) = true := by
  rcases pair with ⟨destination, src⟩
  cases destination <;> cases src <;>
    simp [wMoveSingleNative, stackSlotsWithin] <;> omega

theorem native_move_aux_slots {width : Nat} [NeZero width]
    (moves : List (Sum Nat Nat × Sum Nat Nat)) (kf : Nat × Nat × Nat) :
    stackSlotsWithin kf.2.1 (wMoveAuxNative (width := width) moves kf) = true := by
  induction moves with
  | nil => rfl
  | cons pair rest ih =>
    have first := native_single_move_slots (width := width) pair kf
    cases rest with
    | nil => exact first
    | cons next tail =>
      simp only [wMoveAuxNative, stackSlotsWithin, first, Bool.true_and]
      exact ih

theorem native_parallel_move_slots {width : Nat} [NeZero width]
    (moves : List (Nat × Nat)) (kf : Nat × Nat × Nat) :
    stackSlotsWithin kf.2.1 (wMoveNative (width := width) moves kf) = true :=
  native_move_aux_slots _ kf

theorem allocated_native_slots (config : Compiler.Encoders.Asm.AsmConfigExact 64)
    (perf : Bool) (p : WordLangProgHOL (BitVec 64)) (bs : AppList (BitVec 64) × Nat)
    (kf : Nat × Nat × Nat) (supported : wordStraightFragment p = true) :
    stackSlotsWithin kf.2.1 (compNative config perf p bs kf).1 = true := by
  cases p <;> simp only [wordStraightFragment, Bool.and_eq_true] at supported
  all_goals try contradiction
  case skip => simp only [compNative, stackSlotsWithin]
  case inst instruction =>
    simpa only [compNative] using native_instruction_slots (Compiler.Encoders.Asm.HolInst.ofWordLangInst instruction) kf
  case move priority moves =>
    simpa only [compNative] using native_parallel_move_slots (width := 64) moves kf
  case get destination name =>
    simp only [compNative]
    apply native_write_slots
    intro n
    rfl
  case opCurrHeap operator destination src =>
    simp only [compNative]
    apply native_load_slots
    · exact first_register_slots _ kf
    · apply native_write_slots
      intro n
      rfl
  case seq first second =>
    have one := allocated_native_slots config perf first bs kf supported.1
    have two := allocated_native_slots config perf second
      (compNative config perf first bs kf).2 kf supported.2
    simpa only [compNative, stackSlotsWithin, Bool.and_eq_true] using And.intro one two
termination_by sizeOf p

/-- Directly addressable frames add no slot-expansion multiplier to the native
fragment path bound. Includes arbitrary scheduled parallel moves and spills. -/
theorem allocated_removed_path_bound {C F : Type}
    (config : Compiler.Encoders.Asm.AsmConfigExact 64) (perf jump : Bool)
    (pointer : Nat) (p : WordLangProgHOL (BitVec 64)) (bs : AppList (BitVec 64) × Nat)
    (kf : Nat × Nat × Nat) (small : kf.2.1 ≤ 92)
    (supported : wordStraightFragment p = true)
    (source : StackSemStateFiniteExact 64 C F) :
    StackToLab.pathWork (Compiler.Backend.StackRemove.comp jump riscvConfig.addrOffset pointer
      (compNative config perf p bs kf).1) source ≤ 16 * wordNodeCost p := by
  have native := allocated_native_fragment config perf p bs kf supported
  have slots := allocated_native_slots config perf p bs kf supported
  have direct := direct_removal_units kf.2.1 small _ native.1 slots
  have path := removed_straight_path_bound jump riscvConfig.addrOffset pointer _ native.1 source
  omega

#print axioms allocated_removed_path_bound
#print axioms allocated_native_slots
#print axioms native_instruction_slots
#print axioms native_parallel_move_slots
#print axioms direct_removal_units
#print axioms native_load_slots
end InitECandidate.Runtime.FineCost
