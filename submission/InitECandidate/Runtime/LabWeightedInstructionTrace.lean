import InitECandidate.Runtime.LabControlLocalCost
import InitECandidate.Runtime.LabInstructionTrace

namespace InitECandidate.Runtime.LabToTarget
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.RiscV.Target

/-- Control instruction expansion plus a conservative count of visited line words. -/
def controlWork (base : Nat) (code : LabProgHOL 64) (pc : Nat) : Nat :=
  base + (posVal (pc + 1) 0 code - posVal pc 0 code) / 4

theorem control_count_bound (base : Nat) (code : LabProgHOL 64) (pc : Nat)
    (encoded : List (BitVec 8)) (count : Nat)
    (position : posVal (pc + 1) 0 code = posVal pc 0 code + encoded.length)
    (bound : count ≤ base + encoded.length / 4) : count ≤ controlWork base code pc := by
  have delta : posVal (pc + 1) 0 code - posVal pc 0 code = encoded.length := by omega
  simpa only [controlWork, delta] using bound

/-- Executed label instructions charged by local expansion, not ROM size. -/
inductive WeightedInstructionTrace (code : LabProgHOL 64) {F : Type} : LabSem.State 64 Config F → LabSem.State 64 Config F → Nat → Prop
  | nil (state) : WeightedInstructionTrace code state state 0
  | step (state final : LabSem.State 64 Config F) (i : HolInst 64)
      (bytes : List (BitVec 8)) (n length : Nat)
      (clock : state.clock ≠ 0)
      (fetch : asmFetch state = some (.asm (.asmi (.inst i)) bytes n))
      (success : ¬ (asmInst i state).failed)
      (rest : WeightedInstructionTrace code (incPc (decClock (asmInst i state))) final length) :
      WeightedInstructionTrace code state final (length + LocalCost.instructionWork code state.pc i)

  | jump (state final : LabSem.State 64 Config F) (label : Lab) (pc : Nat) (w : BitVec 64)
      (bytes : List (BitVec 8)) (n length : Nat)
      (clock : state.clock ≠ 0)
      (fetch : asmFetch state = some (.labAsm (.jump label) w bytes n))
      (destination : getPcValue label state = some pc)
      (rest : WeightedInstructionTrace code (LabSem.updPc pc (decClock state)) final length) :
      WeightedInstructionTrace code state final (length + 2)
  | jumpReg (state final : LabSem.State 64 Config F) (r n1 n2 pc : Nat)
      (bytes : List (BitVec 8)) (n length : Nat)
      (clock : state.clock ≠ 0)
      (fetch : asmFetch state = some (.asm (.asmi (.jumpReg r)) bytes n))
      (register : state.regs r = .loc n1 n2)
      (destination : locToPc n1 n2 state.code = some pc)
      (rest : WeightedInstructionTrace code (LabSem.updPc pc (decClock state)) final length) :
      WeightedInstructionTrace code state final (length + 1)

  | branchTaken (state final : LabSem.State 64 Config F) (cmp : HolCmp) (r : Nat)
      (operand : HolRegImm 64) (label : Lab) (pc : Nat) (w : BitVec 64)
      (bytes : List (BitVec 8)) (n length : Nat)
      (clock : state.clock ≠ 0)
      (fetch : asmFetch state = some (.labAsm (.jumpCmp cmp r operand label) w bytes n))
      (chosen : wordSemWordCmp cmp (state.regs r) (LabSem.regImm operand state) = some true)
      (destination : getPcValue label state = some pc)
      (rest : WeightedInstructionTrace code (LabSem.updPc pc (decClock state)) final length) :
      WeightedInstructionTrace code state final (length + 3)
  | branchFallthrough (state final : LabSem.State 64 Config F) (cmp : HolCmp) (r : Nat)
      (operand : HolRegImm 64) (label : Lab) (w : BitVec 64)
      (bytes : List (BitVec 8)) (n length : Nat)
      (clock : state.clock ≠ 0)
      (fetch : asmFetch state = some (.labAsm (.jumpCmp cmp r operand label) w bytes n))
      (chosen : wordSemWordCmp cmp (state.regs r) (LabSem.regImm operand state) = some false)
      (rest : WeightedInstructionTrace code (incPc (decClock state)) final length) :
      WeightedInstructionTrace code state final (length + controlWork 3 code state.pc)
  | locValue (state final : LabSem.State 64 Config F) (r : Nat) (label : Lab) (pc : Nat)
      (w : BitVec 64) (bytes : List (BitVec 8)) (n length : Nat)
      (clock : state.clock ≠ 0)
      (fetch : asmFetch state = some (.labAsm (.locValue r label) w bytes n))
      (destination : getPcValue label state = some pc)
      (rest : WeightedInstructionTrace code (incPc (decClock (LabSem.updReg r (labToLoc label) state))) final length) :
      WeightedInstructionTrace code state final (length + controlWork 2 code state.pc)

theorem weightedInstructionTrace_bounded {F : Type} {start final : LabSem.State 64 Config F} {length : Nat}
    (code : LabProgHOL 64) (trace : WeightedInstructionTrace code start final length)
    (mc : MachineConfig 64 riscv_state RiscVProjection)
    (labs : Spt (Spt Nat)) (p : BitVec 64) (asm : AsmState 64) (machine : riscv_state)
    (target : mc.target = riscvTarget) (encoder : encoderCorrect mc.target)
    (related : stateRel (mc, code, labs, p) start asm machine) :
    ∃ count post asm2, count ≤ length ∧
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
      LocalCost.fetched_inst_work_bound state i mc code labs p asm machine bytes n target fetch success encoder related
    obtain ⟨restCount, post, finalAsm, restBound, restRun, restSearch, finalRel⟩ :=
      ih (shiftInterfer firstCount mc) middleAsm middle target encoder middleRel
    refine ⟨firstCount + restCount, post, finalAsm, ?_, ?_, ?_, ?_⟩
    · omega
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
      LocalCost.fetched_jump_bounded state label pc w mc code labs p asm machine bytes n target fetch destination encoder related
    obtain ⟨restCount, post, finalAsm, restBound, restRun, restSearch, finalRel⟩ :=
      ih (shiftInterfer firstCount mc) _ middle target encoder middleRel
    refine ⟨firstCount + restCount, post, finalAsm, ?_, ?_, ?_, ?_⟩
    · omega
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
      LocalCost.fetched_jumpReg_bounded state r n1 n2 pc mc code labs p asm machine bytes n target fetch register destination encoder related
    obtain ⟨restCount, post, finalAsm, restBound, restRun, restSearch, finalRel⟩ :=
      ih (shiftInterfer firstCount mc) _ middle target encoder middleRel
    refine ⟨firstCount + restCount, post, finalAsm, ?_, ?_, ?_, ?_⟩
    · omega
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
      LocalCost.fetched_branch_taken_bounded state cmp r operand label w mc code labs p asm machine bytes n target fetch encoder related chosen pc destination
    obtain ⟨restCount, post, finalAsm, restBound, restRun, restSearch, finalRel⟩ :=
      ih (shiftInterfer firstCount mc) _ middle target encoder middleRel
    refine ⟨firstCount + restCount, post, finalAsm, ?_, ?_, ?_, ?_⟩
    · omega
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
      LocalCost.fetched_branch_fallthrough_bounded state cmp r operand label w mc code labs p asm machine bytes n target fetch encoder related chosen
    have uniform := control_count_bound 3 code state.pc encoded firstCount position firstBound
    obtain ⟨restCount, post, finalAsm, restBound, restRun, restSearch, finalRel⟩ :=
      ih (shiftInterfer firstCount mc) _ middle target encoder middleRel
    refine ⟨firstCount + restCount, post, finalAsm, ?_, ?_, ?_, ?_⟩
    · omega
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
      LocalCost.fetched_locValue_bounded state r label pc w mc code labs p asm machine bytes n target fetch destination encoder related
    have uniform := control_count_bound 2 code state.pc encoded firstCount position firstBound
    obtain ⟨restCount, post, finalAsm, restBound, restRun, restSearch, finalRel⟩ :=
      ih (shiftInterfer firstCount mc) _ middle target encoder middleRel
    refine ⟨firstCount + restCount, post, finalAsm, ?_, ?_, ?_, ?_⟩
    · omega
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


/-- Erasing costs recovers an ordinary evaluator trace. -/
theorem weightedInstructionTrace_erase {F : Type} {code : LabProgHOL 64}
    {start final : LabSem.State 64 Config F} {work : Nat}
    (trace : WeightedInstructionTrace code start final work) :
    ∃ length, InstructionTrace start final length := by
  induction trace with
  | nil state => exact ⟨0, .nil state⟩
  | step state final i bytes n work clock fetch success rest ih =>
    obtain ⟨length, tail⟩ := ih
    exact ⟨length + 1, .step state final i bytes n length clock fetch success tail⟩
  | jump state final label pc w bytes n work clock fetch destination rest ih =>
    obtain ⟨length, tail⟩ := ih
    exact ⟨length + 1, .jump state final label pc w bytes n length clock fetch destination tail⟩
  | jumpReg state final r n1 n2 pc bytes n work clock fetch register destination rest ih =>
    obtain ⟨length, tail⟩ := ih
    exact ⟨length + 1, .jumpReg state final r n1 n2 pc bytes n length clock fetch register destination tail⟩
  | branchTaken state final cmp r operand label pc w bytes n work clock fetch chosen destination rest ih =>
    obtain ⟨length, tail⟩ := ih
    exact ⟨length + 1, .branchTaken state final cmp r operand label pc w bytes n length clock fetch chosen destination tail⟩
  | branchFallthrough state final cmp r operand label w bytes n work clock fetch chosen rest ih =>
    obtain ⟨length, tail⟩ := ih
    exact ⟨length + 1, .branchFallthrough state final cmp r operand label w bytes n length clock fetch chosen tail⟩
  | locValue state final r label pc w bytes n work clock fetch destination rest ih =>
    obtain ⟨length, tail⟩ := ih
    exact ⟨length + 1, .locValue state final r label pc w bytes n length clock fetch destination tail⟩

theorem weightedInstructionTrace_halt_bounded {F : Type} {start final : LabSem.State 64 Config F} {length : Nat}
    (code : LabProgHOL 64) (trace : WeightedInstructionTrace code start final length)
    (mc : MachineConfig 64 riscv_state RiscVProjection)
    (labs : Spt (Spt Nat)) (p : BitVec 64) (asm : AsmState 64) (machine : riscv_state)
    (target : mc.target = riscvTarget) (encoder : encoderCorrect mc.target)
    (related : stateRel (mc, code, labs, p) start asm machine)
    (w value : BitVec 64) (bytes : List (BitVec 8)) (n : Nat)
    (clock : final.clock ≠ 0)
    (fetch : asmFetch final = some (.labAsm .halt w bytes n))
    (result : final.regs final.ptrReg = .word value) :
    evaluate start = (.halt (if value = 0 then .success else .resourceLimitHit), final) ∧
    ∃ count post, count ≤ length + 17 ∧
      evaluateTargetHOL mc start.ffi count machine =
        (.halt (if value = 0 then .success else .resourceLimitHit), post, final.ffi) := by
  obtain ⟨_, plain⟩ := weightedInstructionTrace_erase trace
  constructor
  · rw [(instructionTrace_source plain).1, evaluate]
    by_cases zero : value = (0#64) <;> simp [clock, fetch, result, zero]
  · obtain ⟨firstCount, middle, middleAsm, firstBound, firstRun, firstSearch, middleRel⟩ :=
      weightedInstructionTrace_bounded code trace mc labs p asm machine target encoder related
    obtain ⟨lastCount, post, lastBound, lastRun⟩ := fetched_halt_bounded final w value
      (shiftInterfer firstCount mc) code labs p middleAsm middle bytes n target fetch result encoder middleRel
    refine ⟨lastCount + firstCount, post, by omega, ?_⟩
    rw [firstRun, lastRun]

theorem weightedInstructionTrace_with_oracle {F : Type} {start final : LabSem.State 64 Config F} {length : Nat}
    (code : LabProgHOL 64) (trace : WeightedInstructionTrace code start final length)
    (mc : MachineConfig 64 riscv_state RiscVProjection)
    (labs : Spt (Spt Nat)) (p : BitVec 64) (asm : AsmState 64) (machine : riscv_state)
    (target : mc.target = riscvTarget) (encoder : encoderCorrect mc.target)
    (related : stateRel (mc, code, labs, p) start asm machine)
    (tie : oracleTie mc machine start) :
    ∃ count post asm2, count ≤ length ∧
      (∀ clock, evaluateTargetHOL mc start.ffi (clock + count) machine =
        evaluateTargetHOL (shiftInterfer count mc) final.ffi clock post) ∧
      stateRel (shiftInterfer count mc, code, labs, p) final asm2 post ∧
      oracleTie (shiftInterfer count mc) post final := by
  obtain ⟨count, post, asm2, bound, run, search, rel⟩ :=
    weightedInstructionTrace_bounded code trace mc labs p asm machine target encoder related
  obtain ⟨_, plain⟩ := weightedInstructionTrace_erase trace
  obtain ⟨io, iofp, cc, ccfp, ffi⟩ := instructionTrace_oracle_fields plain
  refine ⟨count, post, asm2, bound, run, rel, ?_⟩
  apply oracleTie_step mc machine post start final count
  exact ⟨tie, fun clock => by simpa only [ffi] using search clock, io, iofp, cc, ccfp, ffi⟩


end InitECandidate.Runtime.LabToTarget
#print axioms InitECandidate.Runtime.LabToTarget.weightedInstructionTrace_bounded

#print axioms InitECandidate.Runtime.LabToTarget.weightedInstructionTrace_halt_bounded
#print axioms InitECandidate.Runtime.LabToTarget.weightedInstructionTrace_with_oracle
