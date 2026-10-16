import InitECandidate.Runtime.LabProgramBudget

namespace InitECandidate.Runtime.LabToTarget
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.RiscV.Target

/-- Actual instruction and jump paths, using the label evaluator's fetch,
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

  | jump (state final : LabSem.State 64 Config F) (label : Lab) (pc : Nat) (w : BitVec 64)
      (bytes : List (BitVec 8)) (n length : Nat)
      (clock : state.clock ≠ 0)
      (fetch : asmFetch state = some (.labAsm (.jump label) w bytes n))
      (destination : getPcValue label state = some pc)
      (rest : InstructionTrace (LabSem.updPc pc (decClock state)) final length) :
      InstructionTrace state final (length + 1)
  | jumpReg (state final : LabSem.State 64 Config F) (r n1 n2 pc : Nat)
      (bytes : List (BitVec 8)) (n length : Nat)
      (clock : state.clock ≠ 0)
      (fetch : asmFetch state = some (.asm (.asmi (.jumpReg r)) bytes n))
      (register : state.regs r = .loc n1 n2)
      (destination : locToPc n1 n2 state.code = some pc)
      (rest : InstructionTrace (LabSem.updPc pc (decClock state)) final length) :
      InstructionTrace state final (length + 1)

  | branchTaken (state final : LabSem.State 64 Config F) (cmp : HolCmp) (r : Nat)
      (operand : HolRegImm 64) (label : Lab) (pc : Nat) (w : BitVec 64)
      (bytes : List (BitVec 8)) (n length : Nat)
      (clock : state.clock ≠ 0)
      (fetch : asmFetch state = some (.labAsm (.jumpCmp cmp r operand label) w bytes n))
      (chosen : wordSemWordCmp cmp (state.regs r) (LabSem.regImm operand state) = some true)
      (destination : getPcValue label state = some pc)
      (rest : InstructionTrace (LabSem.updPc pc (decClock state)) final length) :
      InstructionTrace state final (length + 1)
  | branchFallthrough (state final : LabSem.State 64 Config F) (cmp : HolCmp) (r : Nat)
      (operand : HolRegImm 64) (label : Lab) (w : BitVec 64)
      (bytes : List (BitVec 8)) (n length : Nat)
      (clock : state.clock ≠ 0)
      (fetch : asmFetch state = some (.labAsm (.jumpCmp cmp r operand label) w bytes n))
      (chosen : wordSemWordCmp cmp (state.regs r) (LabSem.regImm operand state) = some false)
      (rest : InstructionTrace (incPc (decClock state)) final length) :
      InstructionTrace state final (length + 1)
  | locValue (state final : LabSem.State 64 Config F) (r : Nat) (label : Lab) (pc : Nat)
      (w : BitVec 64) (bytes : List (BitVec 8)) (n length : Nat)
      (clock : state.clock ≠ 0)
      (fetch : asmFetch state = some (.labAsm (.locValue r label) w bytes n))
      (destination : getPcValue label state = some pc)
      (rest : InstructionTrace (incPc (decClock (LabSem.updReg r (labToLoc label) state))) final length) :
      InstructionTrace state final (length + 1)

theorem instruction_successor_ffi {F : Type} (state : LabSem.State 64 Config F) (i : HolInst 64) :
    (incPc (decClock (asmInst i state))).ffi = state.ffi := by
  obtain ⟨_, _, _, hffi, _⟩ := asmInstConsts i state
  exact hffi

theorem instruction_ffi {F : Type} (state : LabSem.State 64 Config F) (i : HolInst 64) :
    (asmInst i state).ffi = state.ffi := instruction_successor_ffi state i

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
      (∀ clock, findNextInterference mc start.ffi (clock + count) machine =
        findNextInterference (shiftInterfer count mc) final.ffi clock post) ∧
      stateRel (shiftInterfer count mc, code, labs, p) final asm2 post := by
  induction trace generalizing mc asm machine with
  | nil state =>
    refine ⟨0, machine, asm, by omega, ?_, ?_, ?_⟩
    · intro clock; simp [shiftInterfer_zero]
    · intro clock; simp [shiftInterfer_zero]
    · simpa [shiftInterfer_zero] using related
  | step state final i bytes n length clock fetch success rest ih =>
    obtain ⟨firstCount, middle, middleAsm, firstBound, positive, firstRun, firstSearch, middleRel⟩ :=
      fetched_inst_uniform_bound state i mc code labs p asm machine bytes n target fetch success encoder related
    obtain ⟨restCount, post, finalAsm, restBound, restRun, restSearch, finalRel⟩ :=
      ih (shiftInterfer firstCount mc) middleAsm middle target encoder middleRel
    refine ⟨firstCount + restCount, post, finalAsm, ?_, ?_, ?_, ?_⟩
    · rw [Nat.mul_add, Nat.mul_one]
      omega
    · intro clock
      rw [show clock + (firstCount + restCount) = (clock + restCount) + firstCount by omega,
        firstRun]
      rw [← instruction_successor_ffi state i, restRun, shiftInterfer_twice]
    · intro clock
      rw [show clock + (firstCount + restCount) = (clock + restCount) + firstCount by omega,
        firstSearch]
      simpa only [instruction_ffi, instruction_successor_ffi, LabSem.updPc, LabSem.updReg, incPc, decClock,
        shiftInterfer_twice, Nat.add_comm] using restSearch clock
    · simpa only [shiftInterfer_twice, Nat.add_comm] using finalRel

  | jump state final label pc w bytes n length clock fetch destination rest ih =>
    obtain ⟨firstCount, middle, firstBound, positive, firstRun, firstSearch, middleRel⟩ :=
      fetched_jump_bounded state label pc w mc code labs p asm machine bytes n target fetch destination encoder related
    obtain ⟨restCount, post, finalAsm, restBound, restRun, restSearch, finalRel⟩ :=
      ih (shiftInterfer firstCount mc) _ middle target encoder middleRel
    refine ⟨firstCount + restCount, post, finalAsm, ?_, ?_, ?_, ?_⟩
    · have ceiling : 16 ≤ labStepCeiling code := by unfold labStepCeiling; omega
      rw [Nat.mul_add, Nat.mul_one]
      omega
    · intro clock
      rw [show clock + (firstCount + restCount) = (clock + restCount) + firstCount by omega,
        firstRun]
      simpa only [LabSem.updPc, decClock, shiftInterfer_twice, Nat.add_comm] using restRun clock
    · intro clock
      rw [show clock + (firstCount + restCount) = (clock + restCount) + firstCount by omega,
        firstSearch]
      simpa only [instruction_ffi, instruction_successor_ffi, LabSem.updPc, LabSem.updReg, incPc, decClock,
        shiftInterfer_twice, Nat.add_comm] using restSearch clock
    · simpa only [shiftInterfer_twice, Nat.add_comm] using finalRel
  | jumpReg state final r n1 n2 pc bytes n length clock fetch register destination rest ih =>
    obtain ⟨firstCount, middle, firstBound, positive, firstRun, firstSearch, middleRel⟩ :=
      fetched_jumpReg_bounded state r n1 n2 pc mc code labs p asm machine bytes n target fetch register destination encoder related
    obtain ⟨restCount, post, finalAsm, restBound, restRun, restSearch, finalRel⟩ :=
      ih (shiftInterfer firstCount mc) _ middle target encoder middleRel
    refine ⟨firstCount + restCount, post, finalAsm, ?_, ?_, ?_, ?_⟩
    · have ceiling : 16 ≤ labStepCeiling code := by unfold labStepCeiling; omega
      rw [Nat.mul_add, Nat.mul_one]
      omega
    · intro clock
      rw [show clock + (firstCount + restCount) = (clock + restCount) + firstCount by omega,
        firstRun]
      simpa only [LabSem.updPc, decClock, shiftInterfer_twice, Nat.add_comm] using restRun clock
    · intro clock
      rw [show clock + (firstCount + restCount) = (clock + restCount) + firstCount by omega,
        firstSearch]
      simpa only [instruction_ffi, instruction_successor_ffi, LabSem.updPc, LabSem.updReg, incPc, decClock,
        shiftInterfer_twice, Nat.add_comm] using restSearch clock
    · simpa only [shiftInterfer_twice, Nat.add_comm] using finalRel

  | branchTaken state final cmp r operand label pc w bytes n length clock fetch chosen destination rest ih =>
    obtain ⟨firstCount, middle, firstBound, positive, firstRun, firstSearch, middleRel⟩ :=
      fetched_branch_taken_bounded state cmp r operand label w mc code labs p asm machine bytes n target fetch encoder related chosen pc destination
    have ceiling : 16 ≤ labStepCeiling code := by unfold labStepCeiling; omega
    obtain ⟨restCount, post, finalAsm, restBound, restRun, restSearch, finalRel⟩ :=
      ih (shiftInterfer firstCount mc) _ middle target encoder middleRel
    refine ⟨firstCount + restCount, post, finalAsm, ?_, ?_, ?_, ?_⟩
    · rw [Nat.mul_add, Nat.mul_one]
      omega
    · intro clock
      rw [show clock + (firstCount + restCount) = (clock + restCount) + firstCount by omega,
        firstRun]
      simpa only [LabSem.updPc, LabSem.updReg, incPc, decClock, shiftInterfer_twice, Nat.add_comm] using restRun clock
    · intro clock
      rw [show clock + (firstCount + restCount) = (clock + restCount) + firstCount by omega,
        firstSearch]
      simpa only [instruction_ffi, instruction_successor_ffi, LabSem.updPc, LabSem.updReg, incPc, decClock,
        shiftInterfer_twice, Nat.add_comm] using restSearch clock
    · simpa only [shiftInterfer_twice, Nat.add_comm] using finalRel
  | branchFallthrough state final cmp r operand label w bytes n length clock fetch chosen rest ih =>
    obtain ⟨encoded, firstCount, middle, position, firstBound, positive, firstRun, firstSearch, middleRel⟩ :=
      fetched_branch_fallthrough_bounded state cmp r operand label w mc code labs p asm machine bytes n target fetch encoder related chosen
    have uniform := related_line_count_bound related encoded firstCount position firstBound
    obtain ⟨restCount, post, finalAsm, restBound, restRun, restSearch, finalRel⟩ :=
      ih (shiftInterfer firstCount mc) _ middle target encoder middleRel
    refine ⟨firstCount + restCount, post, finalAsm, ?_, ?_, ?_, ?_⟩
    · rw [Nat.mul_add, Nat.mul_one]
      omega
    · intro clock
      rw [show clock + (firstCount + restCount) = (clock + restCount) + firstCount by omega,
        firstRun]
      simpa only [LabSem.updPc, LabSem.updReg, incPc, decClock, shiftInterfer_twice, Nat.add_comm] using restRun clock
    · intro clock
      rw [show clock + (firstCount + restCount) = (clock + restCount) + firstCount by omega,
        firstSearch]
      simpa only [instruction_ffi, instruction_successor_ffi, LabSem.updPc, LabSem.updReg, incPc, decClock,
        shiftInterfer_twice, Nat.add_comm] using restSearch clock
    · simpa only [shiftInterfer_twice, Nat.add_comm] using finalRel
  | locValue state final r label pc w bytes n length clock fetch destination rest ih =>
    obtain ⟨encoded, firstCount, middle, middleAsm, position, firstBound, positive, firstRun, firstSearch, middleRel⟩ :=
      fetched_locValue_bounded state r label pc w mc code labs p asm machine bytes n target fetch destination encoder related
    have uniform := related_line_count_bound related encoded firstCount position firstBound
    obtain ⟨restCount, post, finalAsm, restBound, restRun, restSearch, finalRel⟩ :=
      ih (shiftInterfer firstCount mc) _ middle target encoder middleRel
    refine ⟨firstCount + restCount, post, finalAsm, ?_, ?_, ?_, ?_⟩
    · rw [Nat.mul_add, Nat.mul_one]
      omega
    · intro clock
      rw [show clock + (firstCount + restCount) = (clock + restCount) + firstCount by omega,
        firstRun]
      simpa only [LabSem.updPc, LabSem.updReg, incPc, decClock, shiftInterfer_twice, Nat.add_comm] using restRun clock
    · intro clock
      rw [show clock + (firstCount + restCount) = (clock + restCount) + firstCount by omega,
        firstSearch]
      simpa only [instruction_ffi, instruction_successor_ffi, LabSem.updPc, LabSem.updReg, incPc, decClock,
        shiftInterfer_twice, Nat.add_comm] using restSearch clock
    · simpa only [shiftInterfer_twice, Nat.add_comm] using finalRel

/-- These traces are faithful evaluator prefixes and cannot contain more
instructions than the source clock allows. -/
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

  | jump state final label pc w bytes n length clock fetch destination rest ih =>
    constructor
    · rw [evaluate]
      simpa only [clock, fetch, destination, reduceCtorEq, ↓reduceIte] using ih.1
    · have tailClock : final.clock + length = state.clock - 1 := ih.2
      omega
  | jumpReg state final r n1 n2 pc bytes n length clock fetch register destination rest ih =>
    constructor
    · rw [evaluate]
      simpa only [clock, ↓reduceIte, fetch, register, destination] using ih.1
    · have tailClock : final.clock + length = state.clock - 1 := ih.2
      omega

  | branchTaken state final cmp r operand label pc w bytes n length clock fetch chosen destination rest ih =>
    constructor
    · rw [evaluate]
      simpa only [clock, ↓reduceIte, fetch, chosen, destination] using ih.1
    · have tailClock : final.clock + length = state.clock - 1 := ih.2
      omega
  | branchFallthrough state final cmp r operand label w bytes n length clock fetch chosen rest ih =>
    constructor
    · rw [evaluate]
      simpa only [clock, ↓reduceIte, fetch, chosen] using ih.1
    · have tailClock : final.clock + length = state.clock - 1 := ih.2
      omega
  | locValue state final r label pc w bytes n length clock fetch destination rest ih =>
    constructor
    · rw [evaluate]
      simpa only [clock, fetch, destination, reduceCtorEq, ↓reduceIte] using ih.1
    · have tailClock : final.clock + length = state.clock - 1 := ih.2
      omega

/-- Instruction and jump traces ending at a halt yield an actual bounded
terminal native evaluation, not merely a related intermediate machine. -/
theorem instructionTrace_halt_bounded {F : Type} {start final : LabSem.State 64 Config F} {length : Nat}
    (trace : InstructionTrace start final length)
    (mc : MachineConfig 64 riscv_state RiscVProjection) (code : LabProgHOL 64)
    (labs : Spt (Spt Nat)) (p : BitVec 64) (asm : AsmState 64) (machine : riscv_state)
    (target : mc.target = riscvTarget) (encoder : encoderCorrect mc.target)
    (related : stateRel (mc, code, labs, p) start asm machine)
    (w value : BitVec 64) (bytes : List (BitVec 8)) (n : Nat)
    (clock : final.clock ≠ 0)
    (fetch : asmFetch final = some (.labAsm .halt w bytes n))
    (result : final.regs final.ptrReg = .word value) :
    evaluate start = (.halt (if value = 0 then .success else .resourceLimitHit), final) ∧
    ∃ count post, count ≤ labStepCeiling code * length + 17 ∧
      evaluateTargetHOL mc start.ffi count machine =
        (.halt (if value = 0 then .success else .resourceLimitHit), post, final.ffi) := by
  constructor
  · rw [(instructionTrace_source trace).1, evaluate]
    by_cases zero : value = (0#64) <;> simp [clock, fetch, result, zero]
  · obtain ⟨firstCount, middle, middleAsm, firstBound, firstRun, firstSearch, middleRel⟩ :=
      instructionTrace_bounded trace mc code labs p asm machine target encoder related
    obtain ⟨lastCount, post, lastBound, lastRun⟩ := fetched_halt_bounded final w value
      (shiftInterfer firstCount mc) code labs p middleAsm middle bytes n target fetch result encoder middleRel
    refine ⟨lastCount + firstCount, post, by omega, ?_⟩
    rw [firstRun, lastRun]

theorem instructionTrace_oracle_fields {F : Type}
    {start final : LabSem.State 64 Config F} {length : Nat}
    (trace : InstructionTrace start final length) :
    final.ioRegs = start.ioRegs ∧ final.ioFpRegs = start.ioFpRegs ∧
      final.ccRegs = start.ccRegs ∧ final.ccFpRegs = start.ccFpRegs ∧ final.ffi = start.ffi := by
  induction trace with
  | nil state => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | step state final i bytes n length clock fetch success rest ih =>
    obtain ⟨_, _, _, hffi, hio, hiofp, hcc, hccfp, _⟩ := asmInstConsts i state
    exact ⟨ih.1.trans hio, ih.2.1.trans hiofp, ih.2.2.1.trans hcc,
      ih.2.2.2.1.trans hccfp, ih.2.2.2.2.trans hffi⟩
  | jump state final label pc w bytes n length clock fetch destination rest ih => exact ih
  | jumpReg state final r n1 n2 pc bytes n length clock fetch register destination rest ih => exact ih
  | branchTaken state final cmp r operand label pc w bytes n length clock fetch chosen destination rest ih => exact ih
  | branchFallthrough state final cmp r operand label w bytes n length clock fetch chosen rest ih => exact ih
  | locValue state final r label pc w bytes n length clock fetch destination rest ih => exact ih

/-- The same bounded trace witness also advances the source/target oracle tie,
so an FFI call may follow this trace without an extra oracle hypothesis. -/
theorem instructionTrace_with_oracle {F : Type} {start final : LabSem.State 64 Config F} {length : Nat}
    (trace : InstructionTrace start final length)
    (mc : MachineConfig 64 riscv_state RiscVProjection) (code : LabProgHOL 64)
    (labs : Spt (Spt Nat)) (p : BitVec 64) (asm : AsmState 64) (machine : riscv_state)
    (target : mc.target = riscvTarget) (encoder : encoderCorrect mc.target)
    (related : stateRel (mc, code, labs, p) start asm machine)
    (tie : oracleTie mc machine start) :
    ∃ count post asm2, count ≤ labStepCeiling code * length ∧
      (∀ clock, evaluateTargetHOL mc start.ffi (clock + count) machine =
        evaluateTargetHOL (shiftInterfer count mc) final.ffi clock post) ∧
      stateRel (shiftInterfer count mc, code, labs, p) final asm2 post ∧
      oracleTie (shiftInterfer count mc) post final := by
  obtain ⟨count, post, asm2, bound, run, search, rel⟩ :=
    instructionTrace_bounded trace mc code labs p asm machine target encoder related
  obtain ⟨io, iofp, cc, ccfp, ffi⟩ := instructionTrace_oracle_fields trace
  refine ⟨count, post, asm2, bound, run, rel, ?_⟩
  apply oracleTie_step mc machine post start final count
  exact ⟨tie, fun clock => by simpa only [ffi] using search clock, io, iofp, cc, ccfp, ffi⟩

end InitECandidate.Runtime.LabToTarget
#print axioms InitECandidate.Runtime.LabToTarget.instructionTrace_bounded

#print axioms InitECandidate.Runtime.LabToTarget.instructionTrace_source

#print axioms InitECandidate.Runtime.LabToTarget.instructionTrace_halt_bounded

#print axioms InitECandidate.Runtime.LabToTarget.instructionTrace_with_oracle
