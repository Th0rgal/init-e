import InitECandidate.Runtime.LabProgramBudget

namespace InitECandidate.Runtime.LabToTarget
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.RiscV.Target

/-- Actual ordinary-instruction paths, using the label evaluator's fetch,
success guard, clock guard and exact recursive successor state. -/
inductive InstructionTrace {F : Type} : LabSem.State 64 Config F → LabSem.State 64 Config F → Nat → Prop
  | nil (state) : InstructionTrace state state 0
  | step (state final : LabSem.State 64 Config F) (i : HolInst 64)
      (bytes : List (BitVec 8)) (n length : Nat)
      (clock : state.clock ≠ 0)
      (fetch : asmFetch state = some (.asm (.asmi (.inst i)) bytes n))
      (success : ¬ (asmInst i state).failed)
      (rest : InstructionTrace (incPc (decClock (asmInst i state))) final length) :
      InstructionTrace state final (length + 1)

theorem instruction_successor_ffi {F : Type} (state : LabSem.State 64 Config F) (i : HolInst 64) :
    (incPc (decClock (asmInst i state))).ffi = state.ffi := by
  obtain ⟨_, _, _, hffi, _⟩ := asmInstConsts i state
  exact hffi

/-- Recursively compose the concrete label-instruction simulations. The
native budget grows linearly in the actual source trace length. -/
theorem instructionTrace_bounded {F : Type} {start final : LabSem.State 64 Config F} {length : Nat}
    (trace : InstructionTrace start final length)
    (mc : MachineConfig 64 riscv_state RiscVProjection) (code : LabProgHOL 64)
    (labs : Spt (Spt Nat)) (p : BitVec 64) (asm : AsmState 64) (machine : riscv_state)
    (target : mc.target = riscvTarget) (encoder : encoderCorrect mc.target)
    (related : stateRel (mc, code, labs, p) start asm machine) :
    ∃ count post asm2, count ≤ labStepCeiling code * length ∧
      (∀ clock, evaluateTargetHOL mc start.ffi (clock + count) machine =
        evaluateTargetHOL (shiftInterfer count mc) final.ffi clock post) ∧
      stateRel (shiftInterfer count mc, code, labs, p) final asm2 post := by
  induction trace generalizing mc asm machine with
  | nil state =>
    refine ⟨0, machine, asm, by omega, ?_, ?_⟩
    · intro clock; simp [shiftInterfer_zero]
    · simpa [shiftInterfer_zero] using related
  | step state final i bytes n length clock fetch success rest ih =>
    obtain ⟨firstCount, middle, middleAsm, firstBound, positive, firstRun, middleRel⟩ :=
      fetched_inst_uniform_bound state i mc code labs p asm machine bytes n target fetch success encoder related
    obtain ⟨restCount, post, finalAsm, restBound, restRun, finalRel⟩ :=
      ih (shiftInterfer firstCount mc) middleAsm middle target encoder middleRel
    refine ⟨firstCount + restCount, post, finalAsm, ?_, ?_, ?_⟩
    · rw [Nat.mul_add, Nat.mul_one]
      omega
    · intro clock
      rw [show clock + (firstCount + restCount) = (clock + restCount) + firstCount by omega,
        firstRun]
      rw [← instruction_successor_ffi state i, restRun, shiftInterfer_twice]
    · simpa only [shiftInterfer_twice, Nat.add_comm] using finalRel

/-- These traces are faithful evaluator prefixes and cannot contain more
ordinary instructions than the source clock allows. -/
theorem instructionTrace_source {F : Type} {start final : LabSem.State 64 Config F} {length : Nat}
    (trace : InstructionTrace start final length) :
    evaluate start = evaluate final ∧ final.clock + length = start.clock := by
  induction trace with
  | nil state => exact ⟨rfl, by omega⟩
  | step state final i bytes n length clock fetch success rest ih =>
    constructor
    · rw [evaluate]
      simp only [clock, ↓reduceIte, fetch, success, Bool.false_eq_true, ↓reduceIte]
      exact ih.1
    · have clockEq : (incPc (decClock (asmInst i state))).clock = state.clock - 1 := by
        obtain ⟨_, _, sameClock, _⟩ := asmInstConsts i state
        simp only [incPc, decClock, sameClock]
      have tailClock := ih.2
      rw [clockEq] at tailClock
      omega

end InitECandidate.Runtime.LabToTarget
#print axioms InitECandidate.Runtime.LabToTarget.instructionTrace_bounded

#print axioms InitECandidate.Runtime.LabToTarget.instructionTrace_source
