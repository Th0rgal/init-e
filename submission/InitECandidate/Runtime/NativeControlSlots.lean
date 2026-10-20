import InitECandidate.Runtime.NativeFrameSlots
import Flapjack.Compiler.Backend.WordToStack.NativePrograms
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordToStackRegFormat

/-- Checks every syntactically nested frame access, including both branches,
loop bodies, and call continuations/handlers. Callee code has its own frame. -/
def stackControlSlotsWithin {width : Nat} [NeZero width] (frame : Nat) : HolProg width → Bool
  | .stackLoad _ slot | .stackStore _ slot => decide (slot ≤ frame)
  | .seq first second | .ite _ _ _ first second =>
      stackControlSlotsWithin frame first && stackControlSlotsWithin frame second
  | .loop body => stackControlSlotsWithin frame body
  | .call ret _ handler =>
      (match ret with
        | none => true
        | some (body, _, _, _) => stackControlSlotsWithin frame body) &&
      (match handler with
        | none => true
        | some (body, _, _) => stackControlSlotsWithin frame body)
  | _ => true
termination_by p => sizeOf p

/-- Existing leaf/frame proofs lift without weakening their slot bound. -/
theorem control_slots_of_straight {width : Nat} [NeZero width] (frame : Nat) (p : HolProg width)
    (straight : stackStraightLine p = true) :
    stackControlSlotsWithin frame p = stackSlotsWithin frame p := by
  cases p <;> simp only [stackStraightLine, Bool.and_eq_true] at straight
  all_goals try contradiction
  all_goals try (simp only [stackControlSlotsWithin, stackSlotsWithin])
  case seq first second =>
    simp only [stackControlSlotsWithin, stackSlotsWithin,
      control_slots_of_straight frame first straight.1,
      control_slots_of_straight frame second straight.2]
termination_by sizeOf p

theorem native_control_load_slots {width : Nat} [NeZero width]
    (loads : List (Nat × Nat)) (p : HolProg width) (frame : Nat)
    (bounded : loads.all (fun entry => decide (entry.2 ≤ frame)) = true)
    (body : stackControlSlotsWithin frame p = true) :
    stackControlSlotsWithin frame (wStackLoadNative loads p) = true := by
  induction loads with
  | nil => exact body
  | cons pair rest ih =>
    rcases pair with ⟨register, slot⟩
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at bounded
    simp only [wStackLoadNative, stackControlSlotsWithin, Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨bounded.1, ih bounded.2⟩

/-- Native control skeleton whose leaves are the already certified allocated
fragments. Calls/returns and their frame transitions are separate obligations. -/
def wordNativeControlFragment : WordLangProgHOL (BitVec 64) → Bool
  | .seq first second | .ite _ _ _ first second =>
      wordNativeControlFragment first && wordNativeControlFragment second
  | .loop _ body _ | .mustTerminate body => wordNativeControlFragment body
  | .tick | .break _ | .continue _ => true
  | p => wordStraightFragment p
termination_by p => sizeOf p

/-- Native conditional reloads do not acquire a frame-size factor. This holds
for either register operands or immediate materialization, whether encodable
or not. Both compiled branches retain their own recursive frame-access proof. -/
theorem native_control_slots (config : Compiler.Encoders.Asm.AsmConfigExact 64)
    (perf : Bool) (p : WordLangProgHOL (BitVec 64)) (bs : AppList (BitVec 64) × Nat)
    (kf : Nat × Nat × Nat) (supported : wordNativeControlFragment p = true) :
    stackControlSlotsWithin kf.2.1 (compNative config perf p bs kf).1 = true := by
  cases p <;> simp only [wordNativeControlFragment, wordStraightFragment, Bool.and_eq_true] at supported
  all_goals try contradiction
  case seq first second =>
    have one := native_control_slots config perf first bs kf supported.1
    have two := native_control_slots config perf second
      (compNative config perf first bs kf).2 kf supported.2
    simpa only [compNative, stackControlSlotsWithin, Bool.and_eq_true] using And.intro one two
  case ite comparison register operand first second =>
    have one := native_control_slots config perf first bs kf supported.1
    have two := native_control_slots config perf second
      (compNative config perf first bs kf).2 kf supported.2
    cases operand with
    | reg r =>
      simp only [compNative]
      apply native_control_load_slots
      · simp only [List.all_append, first_register_slots, second_register_slots, Bool.true_and]
      · simp only [stackControlSlotsWithin, one, two, Bool.true_and]
    | imm value =>
      simp only [compNative]
      split
      · apply native_control_load_slots
        · exact first_register_slots _ kf
        · simp only [stackControlSlotsWithin, one, two, Bool.true_and]
      · simp only [stackControlSlotsWithin, Bool.true_and]
        apply native_control_load_slots
        · exact first_register_slots _ kf
        · simp only [stackControlSlotsWithin, one, two, Bool.true_and]
  case loop live body exits =>
    simpa only [compNative, stackControlSlotsWithin] using
      native_control_slots config perf body bs kf supported
  case mustTerminate body =>
    simpa only [compNative] using native_control_slots config perf body bs kf supported
  case tick => simp only [compNative, stackControlSlotsWithin]
  case «break» level => simp only [compNative, stackControlSlotsWithin]
  case «continue» level => simp only [compNative, stackControlSlotsWithin]
  all_goals
    rw [control_slots_of_straight _ _ (allocated_native_fragment config perf _ bs kf (by simp only [wordStraightFragment])).1]
    exact allocated_native_slots config perf _ bs kf (by simp only [wordStraightFragment])
termination_by sizeOf p

/-- Frame offsets nested in the code tree; excludes dynamically looked-up
callee bodies, which must be checked under their own frame. -/
def stackControlFrameOffsets {width : Nat} [NeZero width] : HolProg width → List Nat
  | .stackLoad _ slot | .stackStore _ slot => [slot]
  | .seq first second | .ite _ _ _ first second =>
      stackControlFrameOffsets first ++ stackControlFrameOffsets second
  | .loop body => stackControlFrameOffsets body
  | .call ret _ handler =>
      (match ret with
        | none => []
        | some (body, _, _, _) => stackControlFrameOffsets body) ++
      (match handler with
        | none => []
        | some (body, _, _) => stackControlFrameOffsets body)
  | _ => []
termination_by p => sizeOf p

theorem control_slots_offsets {width : Nat} [NeZero width] (frame : Nat) (p : HolProg width)
    (bounded : stackControlSlotsWithin frame p = true) :
    ∀ slot ∈ stackControlFrameOffsets p, slot ≤ frame := by
  cases p
  all_goals try (simp only [stackControlFrameOffsets, List.not_mem_nil, false_implies, implies_true])
  case stackLoad register offset =>
    simp only [stackControlSlotsWithin, decide_eq_true_eq] at bounded
    simpa only [stackControlFrameOffsets, List.mem_singleton, forall_eq] using bounded
  case stackStore register offset =>
    simp only [stackControlSlotsWithin, decide_eq_true_eq] at bounded
    simpa only [stackControlFrameOffsets, List.mem_singleton, forall_eq] using bounded
  case seq first second =>
    simp only [stackControlSlotsWithin, Bool.and_eq_true] at bounded
    intro slot member
    rcases List.mem_append.mp member with one | two
    · exact control_slots_offsets frame first bounded.1 slot one
    · exact control_slots_offsets frame second bounded.2 slot two
  case ite comparison register operand first second =>
    simp only [stackControlSlotsWithin, Bool.and_eq_true] at bounded
    intro slot member
    rcases List.mem_append.mp member with one | two
    · exact control_slots_offsets frame first bounded.1 slot one
    · exact control_slots_offsets frame second bounded.2 slot two
  case loop body =>
    simpa only [stackControlFrameOffsets] using
      control_slots_offsets frame body (by simpa only [stackControlSlotsWithin] using bounded)
  case call ret destination handler =>
    cases hret : ret with
    | none =>
      cases hhandler : handler with
      | none => simp only [hret, hhandler, stackControlFrameOffsets, List.append_nil,
          List.not_mem_nil, false_implies, implies_true]
      | some handlerTuple =>
        rcases handlerEq : handlerTuple with ⟨body, l1, l2⟩
        simp only [hret, hhandler, handlerEq, stackControlSlotsWithin, Bool.true_and] at bounded
        simpa only [hret, hhandler, handlerEq, stackControlFrameOffsets, List.nil_append] using
          control_slots_offsets frame body bounded
    | some returnTuple =>
      rcases returnEq : returnTuple with ⟨body, link, l1, l2⟩
      cases hhandler : handler with
      | none =>
        simp only [hret, hhandler, returnEq, stackControlSlotsWithin, Bool.and_true] at bounded
        simpa only [hret, hhandler, returnEq, stackControlFrameOffsets, List.append_nil] using
          control_slots_offsets frame body bounded
      | some handlerTuple =>
        rcases handlerEq : handlerTuple with ⟨handlerBody, h1, h2⟩
        simp only [hret, hhandler, returnEq, handlerEq, stackControlSlotsWithin,
          Bool.and_eq_true] at bounded
        intro slot member
        simp only [hret, hhandler, returnEq, handlerEq, stackControlFrameOffsets] at member
        rcases List.mem_append.mp member with one | two
        · exact control_slots_offsets frame body bounded.1 slot one
        · exact control_slots_offsets frame handlerBody bounded.2 slot two
termination_by sizeOf p
decreasing_by
  all_goals simp_all +zetaDelta [Prod.mk.sizeOf_spec, Option.some.sizeOf_spec]
  all_goals omega

/-- Every nested spill/reload of a supported native control skeleton uses the
single-instruction direct offset case of the pinned RISC-V stack remover. -/
theorem native_control_direct_offsets (config : Compiler.Encoders.Asm.AsmConfigExact 64)
    (perf : Bool) (p : WordLangProgHOL (BitVec 64)) (bs : AppList (BitVec 64) × Nat)
    (kf : Nat × Nat × Nat) (supported : wordNativeControlFragment p = true)
    (small : kf.2.1 ≤ 92) :
    ∀ slot ∈ stackControlFrameOffsets (compNative config perf p bs kf).1,
      Compiler.Encoders.Asm.asmOffsetOkExact 0
        Compiler.Encoders.RiscV.Target.riscvConfig.addrOffset
        (Compiler.Backend.StackRemove.wordOffset slot) = true := by
  intro slot member
  have bounded := control_slots_offsets kf.2.1 _
    (native_control_slots config perf p bs kf supported) slot member
  exact small_frame_slot_direct slot (Nat.le_trans bounded small)

/-- The actual native function compiler supplies the same computed frame to
its prologue and body; the prologue introduces no frame-relative access. -/
theorem native_control_program_slots
    (config : Compiler.Encoders.Asm.AsmConfigExact 64) (perf : Bool)
    (p : WordLangProgHOL (BitVec 64)) (arguments registers : Nat)
    (bs : AppList (BitVec 64) × Nat) (supported : wordNativeControlFragment p = true) :
    let result := compileProgNative config perf p arguments registers bs
    stackControlSlotsWithin result.2.1 result.1 = true := by
  simp only [compileProgNative]
  simp only [stackControlSlotsWithin, Bool.true_and]
  exact native_control_slots config perf p bs
    (registers,
      (if max (maxVarHOL p / 2 + 1 - registers) (arguments - registers) = 0 then 0
       else max (maxVarHOL p / 2 + 1 - registers) (arguments - registers) + 1),
      max (maxVarHOL p / 2 + 1 - registers) (arguments - registers)) supported

#print axioms native_control_program_slots
#print axioms native_control_direct_offsets
#print axioms control_slots_offsets
#print axioms native_control_slots
#print axioms control_slots_of_straight
end InitECandidate.Runtime.FineCost
