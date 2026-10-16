import InitECandidate.Runtime.LabSharedBudget
import InitECandidate.Runtime.LabInstructionTrace
import InitECandidate.Runtime.LabFfiBudget

namespace InitECandidate.Runtime.LabToTarget
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Basis.Pure.MlString

/-- Actual source control-flow segments interleaved with returning FFI calls. -/
inductive MixedTrace {F : Type} : LabSem.State 64 Config F → LabSem.State 64 Config F → Nat → Prop
  | nil (state) : MixedTrace state state 0
  | ordinary (start middle final : LabSem.State 64 Config F) (length restLength : Nat)
      (segment : InstructionTrace start middle length)
      (rest : MixedTrace middle final restLength) : MixedTrace start final (length + restLength)
  | ffi (state final : LabSem.State 64 Config F) (name : MlString) (w : BitVec 64)
      (bytes : List (BitVec 8)) (n : Nat)
      (len start len2 start2 : BitVec 64) (conf bytes2 : List (BitVec 8))
      (n1 n2 newPc : Nat) (newFfi : HolFfiState F) (newBytes : List (BitVec 8)) (length : Nat)
      (clock : state.clock ≠ 0)
      (fetch : asmFetch state = some (.labAsm (.callFFI name) w bytes n))
      (hlen : state.regs state.lenReg = .word len) (hptr : state.regs state.ptrReg = .word start)
      (hlen2 : state.regs state.len2Reg = .word len2) (hptr2 : state.regs state.ptr2Reg = .word start2)
      (read1 : readBytearrayWordHOL start len.toNat
        (memLoadByteAuxExact state.memory state.memDomain state.be) = some conf)
      (read2 : readBytearrayWordHOL start2 len2.toNat
        (memLoadByteAuxExact state.memory state.memDomain state.be) = some bytes2)
      (link : state.regs state.linkReg = .loc n1 n2)
      (destination : locToPc n1 n2 state.code = some newPc)
      (call : callFFIHOL state.ffi (.extCall name) conf bytes2 = .ret newFfi newBytes)
      (rest : MixedTrace (ffiReturnedSource state name start2 newBytes newPc newFfi) final length) :
      MixedTrace state final (length + 1)

  | shared (state final : LabSem.State 64 Config F) (m : HolMemop) (r base : Nat) (off : BitVec 64)
      (bytes : List (BitVec 8)) (n : Nat) (ffi : HolFfiState F) (returned : List (BitVec 8))
      (next : LabSem.State 64 Config F) (length : Nat)
      (clock : state.clock ≠ 0)
      (fetch : asmFetch state = some (.asm (.shareMem m r (.addr base off)) bytes n))
      (operation : shareMemOp m r (.addr base off) state = some (.ret ffi returned, next))
      (rest : MixedTrace { next with ioRegs := holShiftSeq 1 next.ioRegs, ioFpRegs := holShiftSeq 1 next.ioFpRegs } final length) : MixedTrace state final (length + 1)

/-- Bounded simulation of arbitrarily many returning FFI calls interleaved
with actual control-flow traces. The final configuration retains consumed
native and FFI interference oracles rather than discarding either shift. -/
theorem mixedTrace_bounded {F : Type} {start final : LabSem.State 64 Config F} {length : Nat}
    (trace : MixedTrace start final length)
    (mc : MachineConfig 64 riscv_state RiscVProjection) (code : LabProgHOL 64)
    (labs : Spt (Spt Nat)) (p : BitVec 64) (asm : AsmState 64) (machine : riscv_state)
    (target : mc.target = riscvTarget) (encoder : encoderCorrect mc.target)
    (related : stateRel (mc, code, labs, p) start asm machine) (tie : oracleTie mc machine start) :
    ∃ count post asm2 finalConfig, count ≤ (labStepCeiling code + 1) * length ∧
      finalConfig.target = riscvTarget ∧ encoderCorrect finalConfig.target ∧
      (∀ clock, evaluateTargetHOL mc start.ffi (clock + count) machine =
        evaluateTargetHOL finalConfig final.ffi clock post) ∧
      stateRel (finalConfig, code, labs, p) final asm2 post ∧ oracleTie finalConfig post final := by
  induction trace generalizing mc asm machine with
  | nil state =>
    exact ⟨0, machine, asm, mc, by omega, target, encoder, fun _ => by simp, related, tie⟩
  | ordinary start middle final length restLength segment rest ih =>
    obtain ⟨firstCount, middleMachine, middleAsm, firstBound, firstRun, middleRel, middleTie⟩ :=
      instructionTrace_with_oracle segment mc code labs p asm machine target encoder related tie
    obtain ⟨restCount, post, finalAsm, finalConfig, restBound, finalTarget, finalEncoder,
        restRun, finalRel, finalTie⟩ :=
      ih (shiftInterfer firstCount mc) middleAsm middleMachine target encoder middleRel middleTie
    refine ⟨firstCount + restCount, post, finalAsm, finalConfig, ?_, finalTarget, finalEncoder,
      ?_, finalRel, finalTie⟩
    · have firstBound' : firstCount ≤ (labStepCeiling code + 1) * length :=
        firstBound.trans (Nat.mul_le_mul_right length (by omega))
      rw [Nat.mul_add]
      omega
    · intro clock
      rw [show clock + (firstCount + restCount) = (clock + restCount) + firstCount by omega,
        firstRun, restRun]
  | ffi state final name w bytes n len start len2 start2 conf bytes2 n1 n2 newPc newFfi newBytes
      length clock fetch hlen hptr hlen2 hptr2 read1 read2 link destination call rest ih =>
    obtain ⟨firstCount, entry, middleAsm, firstBound, firstRun, middleRel, middleTie⟩ :=
      fetched_ffi_return_bounded state name w mc code labs p asm machine bytes n len start len2 start2
        conf bytes2 target fetch hlen hptr hlen2 hptr2 read1 read2 encoder related n1 n2 newPc newFfi
        newBytes tie link destination call
    obtain ⟨restCount, post, finalAsm, finalConfig, restBound, finalTarget, finalEncoder,
        restRun, finalRel, finalTie⟩ :=
      ih { shiftInterfer firstCount mc with ffiInterfer := holShiftSeq 1 mc.ffiInterfer }
        middleAsm _ target encoder middleRel middleTie
    refine ⟨firstCount + 1 + restCount, post, finalAsm, finalConfig, ?_, finalTarget, finalEncoder,
      ?_, finalRel, finalTie⟩
    · have ceiling : 17 ≤ labStepCeiling code + 1 := by unfold labStepCeiling; omega
      rw [Nat.mul_add, Nat.mul_one]
      omega
    · intro clock
      rw [show clock + (firstCount + 1 + restCount) = (clock + restCount) + (firstCount + 1) by omega,
        firstRun]
      exact restRun clock

  | shared state final m r base off bytes n ffi returned next length clock fetch operation rest ih =>
    obtain ⟨index, middleAsm, firstRun, middleRel, middleTie, nextClock, nextCode, nextFfi⟩ :=
      shared_return_native state m r base off bytes n mc code labs p asm machine fetch related tie ffi returned next operation
    obtain ⟨restCount, post, finalAsm, finalConfig, restBound, finalTarget, finalEncoder,
        restRun, finalRel, finalTie⟩ :=
      ih { mc with ffiInterfer := holShiftSeq 1 mc.ffiInterfer } middleAsm _ target encoder middleRel middleTie
    refine ⟨1 + restCount, post, finalAsm, finalConfig, ?_, finalTarget, finalEncoder, ?_, finalRel, finalTie⟩
    · have ceiling : 1 ≤ labStepCeiling code + 1 := by omega
      rw [Nat.mul_add, Nat.mul_one]
      omega
    · intro clock
      rw [show clock + (1 + restCount) = (clock + restCount) + 1 by omega, firstRun]
      simpa only [nextFfi] using restRun clock

theorem mixedTrace_source {F : Type} {start final : LabSem.State 64 Config F} {length : Nat}
    (trace : MixedTrace start final length) :
    evaluate start = evaluate final ∧ final.clock + length = start.clock := by
  induction trace with
  | nil state => exact ⟨rfl, by omega⟩
  | ordinary start middle final length restLength segment rest ih =>
    have source := instructionTrace_source segment
    exact ⟨source.1.trans ih.1, by omega⟩
  | ffi state final name w bytes n len start len2 start2 conf bytes2 n1 n2 newPc newFfi newBytes
      length clock fetch hlen hptr hlen2 hptr2 read1 read2 link destination call rest ih =>
    constructor
    · rw [evaluate]
      simp only [clock, ↓reduceIte, fetch, hlen, hptr, hlen2, hptr2, link,
        read1, read2, destination, call]
      exact ih.1
    · have tailClock : final.clock + length = state.clock - 1 := ih.2
      omega

  | shared state final m r base off bytes n ffi returned next length clock fetch operation rest ih =>
    constructor
    · rw [evaluate]
      simp only [clock, ↓reduceIte, fetch]
      rw [operation]
      exact ih.1
    · have nextClock := shareMemOp_ret_clock m r (.addr base off) state next ffi returned operation
      have tailClock : final.clock + length = next.clock := ih.2
      omega

/-- A mixed control/FFI trace ending at a real halt has a native terminal
bound linear in the initial label-evaluator clock. -/
theorem mixedTrace_halt_bounded {F : Type} {start final : LabSem.State 64 Config F} {length : Nat}
    (trace : MixedTrace start final length)
    (mc : MachineConfig 64 riscv_state RiscVProjection) (code : LabProgHOL 64)
    (labs : Spt (Spt Nat)) (p : BitVec 64) (asm : AsmState 64) (machine : riscv_state)
    (target : mc.target = riscvTarget) (encoder : encoderCorrect mc.target)
    (related : stateRel (mc, code, labs, p) start asm machine) (tie : oracleTie mc machine start)
    (w value : BitVec 64) (bytes : List (BitVec 8)) (n : Nat)
    (clock : final.clock ≠ 0)
    (fetch : asmFetch final = some (.labAsm .halt w bytes n))
    (result : final.regs final.ptrReg = .word value) :
    evaluate start = (.halt (if value = 0 then .success else .resourceLimitHit), final) ∧
    ∃ count post, count ≤ (labStepCeiling code + 1) * start.clock ∧
      evaluateTargetHOL mc start.ffi count machine =
        (.halt (if value = 0 then .success else .resourceLimitHit), post, final.ffi) := by
  constructor
  · rw [(mixedTrace_source trace).1, evaluate]
    by_cases zero : value = (0#64) <;> simp [clock, fetch, result, zero]
  · obtain ⟨firstCount, middle, middleAsm, finalConfig, firstBound, finalTarget,
        finalEncoder, firstRun, middleRel, middleTie⟩ :=
      mixedTrace_bounded trace mc code labs p asm machine target encoder related tie
    obtain ⟨lastCount, post, lastBound, lastRun⟩ := fetched_halt_bounded final w value
      finalConfig code labs p middleAsm middle bytes n finalTarget fetch result finalEncoder middleRel
    refine ⟨lastCount + firstCount, post, ?_, ?_⟩
    · have sourceClock := (mixedTrace_source trace).2
      have lengthBound : length + 1 ≤ start.clock := by omega
      have ceiling : 17 ≤ labStepCeiling code + 1 := by unfold labStepCeiling; omega
      have multiplied := Nat.mul_le_mul_left (labStepCeiling code + 1) lengthBound
      rw [Nat.mul_add, Nat.mul_one] at multiplied
      omega
    · rw [firstRun, lastRun]

theorem mixedTrace_ffi_final_bounded {F : Type}
    {initial terminal : LabSem.State 64 Config F} {length : Nat}
    (trace : MixedTrace initial terminal length)
    (mc : MachineConfig 64 riscv_state RiscVProjection) (code : LabProgHOL 64)
    (labs : Spt (Spt Nat)) (p : BitVec 64) (asm : AsmState 64) (machine : riscv_state)
    (target : mc.target = riscvTarget) (encoder : encoderCorrect mc.target)
    (related : stateRel (mc, code, labs, p) initial asm machine) (tie : oracleTie mc machine initial)
    (name : MlString) (w : BitVec 64) (bytes : List (BitVec 8)) (n : Nat)
    (len start len2 start2 : BitVec 64) (conf bytes2 : List (BitVec 8))
    (n1 n2 pc : Nat) (event : HolFinalEvent)
    (clock : terminal.clock ≠ 0)
    (fetch : asmFetch terminal = some (.labAsm (.callFFI name) w bytes n))
    (hlen : terminal.regs terminal.lenReg = .word len) (hptr : terminal.regs terminal.ptrReg = .word start)
    (hlen2 : terminal.regs terminal.len2Reg = .word len2) (hptr2 : terminal.regs terminal.ptr2Reg = .word start2)
    (read1 : readBytearrayWordHOL start len.toNat
      (memLoadByteAuxExact terminal.memory terminal.memDomain terminal.be) = some conf)
    (read2 : readBytearrayWordHOL start2 len2.toNat
      (memLoadByteAuxExact terminal.memory terminal.memDomain terminal.be) = some bytes2)
    (link : terminal.regs terminal.linkReg = .loc n1 n2)
    (destination : locToPc n1 n2 terminal.code = some pc)
    (call : callFFIHOL terminal.ffi (.extCall name) conf bytes2 = .final event) :
    evaluate initial = (.halt (.ffiOutcome event), terminal) ∧
    ∃ count post, count ≤ (labStepCeiling code + 1) * initial.clock ∧
      evaluateTargetHOL mc initial.ffi count machine = (.halt (.ffiOutcome event), post, terminal.ffi) := by
  constructor
  · rw [(mixedTrace_source trace).1, evaluate]
    simp only [clock, ↓reduceIte, fetch, hlen, hptr, hlen2, hptr2, link,
      read1, read2, destination, call]
  · obtain ⟨firstCount, middle, middleAsm, finalConfig, firstBound, finalTarget,
        finalEncoder, firstRun, middleRel, middleTie⟩ :=
      mixedTrace_bounded trace mc code labs p asm machine target encoder related tie
    obtain ⟨lastCount, post, lastBound, lastRun⟩ := fetched_ffi_final_bounded terminal name w
      finalConfig code labs p middleAsm middle bytes n len start len2 start2 conf bytes2 finalTarget fetch
      hlen hptr hlen2 hptr2 read1 read2 finalEncoder middleRel event call
    refine ⟨lastCount + firstCount, post, ?_, ?_⟩
    · have sourceClock := (mixedTrace_source trace).2
      have lengthBound : length + 1 ≤ initial.clock := by omega
      have ceiling : 17 ≤ labStepCeiling code + 1 := by unfold labStepCeiling; omega
      have multiplied := Nat.mul_le_mul_left (labStepCeiling code + 1) lengthBound
      rw [Nat.mul_add, Nat.mul_one] at multiplied
      omega
    · rw [firstRun, lastRun]

end InitECandidate.Runtime.LabToTarget
#print axioms InitECandidate.Runtime.LabToTarget.mixedTrace_bounded

#print axioms InitECandidate.Runtime.LabToTarget.mixedTrace_source

#print axioms InitECandidate.Runtime.LabToTarget.mixedTrace_halt_bounded

#print axioms InitECandidate.Runtime.LabToTarget.mixedTrace_ffi_final_bounded
