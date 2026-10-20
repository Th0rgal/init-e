import InitECandidate.Runtime.LabSharedBudget
import InitECandidate.Runtime.LabWeightedInstructionTrace
import InitECandidate.Runtime.LabFfiBudget

namespace InitECandidate.Runtime.LabToTarget
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Basis.Pure.MlString

/-- Local native work for ordinary execution, FFI returns and shared-memory events. -/
inductive WeightedMixedTrace (code : LabProgHOL 64) {F : Type} : LabSem.State 64 Config F → LabSem.State 64 Config F → Nat → Prop
  | nil (state) : WeightedMixedTrace code state state 0
  | ordinary (start middle final : LabSem.State 64 Config F) (length restLength : Nat)
      (segment : WeightedInstructionTrace code start middle length)
      (rest : WeightedMixedTrace code middle final restLength) : WeightedMixedTrace code start final (length + restLength)
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
      (rest : WeightedMixedTrace code (ffiReturnedSource state name start2 newBytes newPc newFfi) final length) :
      WeightedMixedTrace code state final (length + 17)

  | shared (state final : LabSem.State 64 Config F) (m : HolMemop) (r base : Nat) (off : BitVec 64)
      (bytes : List (BitVec 8)) (n : Nat) (ffi : HolFfiState F) (returned : List (BitVec 8))
      (next : LabSem.State 64 Config F) (length : Nat)
      (clock : state.clock ≠ 0)
      (fetch : asmFetch state = some (.asm (.shareMem m r (.addr base off)) bytes n))
      (operation : shareMemOp m r (.addr base off) state = some (.ret ffi returned, next))
      (rest : WeightedMixedTrace code { next with ioRegs := holShiftSeq 1 next.ioRegs, ioFpRegs := holShiftSeq 1 next.ioFpRegs } final length) : WeightedMixedTrace code state final (length + 1)

theorem weightedMixedTrace_bounded {F : Type} {start final : LabSem.State 64 Config F} {length : Nat}
    (code : LabProgHOL 64) (trace : WeightedMixedTrace code start final length)
    (mc : MachineConfig 64 riscv_state RiscVProjection)
    (labs : Spt (Spt Nat)) (p : BitVec 64) (asm : AsmState 64) (machine : riscv_state)
    (target : mc.target = riscvTarget) (encoder : encoderCorrect mc.target)
    (related : stateRel (mc, code, labs, p) start asm machine) (tie : oracleTie mc machine start) :
    ∃ count post asm2 finalConfig, count ≤ length ∧
      finalConfig.target = riscvTarget ∧ encoderCorrect finalConfig.target ∧
      (∀ clock, evaluateTargetHOL mc start.ffi (clock + count) machine =
        evaluateTargetHOL finalConfig final.ffi clock post) ∧
      stateRel (finalConfig, code, labs, p) final asm2 post ∧ oracleTie finalConfig post final := by
  induction trace generalizing mc asm machine with
  | nil state =>
    exact ⟨0, machine, asm, mc, by omega, target, encoder, fun _ => by simp, related, tie⟩
  | ordinary start middle final length restLength segment rest ih =>
    obtain ⟨firstCount, middleMachine, middleAsm, firstBound, firstRun, middleRel, middleTie⟩ :=
      weightedInstructionTrace_with_oracle code segment mc labs p asm machine target encoder related tie
    obtain ⟨restCount, post, finalAsm, finalConfig, restBound, finalTarget, finalEncoder,
        restRun, finalRel, finalTie⟩ :=
      ih (shiftInterfer firstCount mc) middleAsm middleMachine target encoder middleRel middleTie
    refine ⟨firstCount + restCount, post, finalAsm, finalConfig, ?_, finalTarget, finalEncoder,
      ?_, finalRel, finalTie⟩
    · omega
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
    · omega
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
    · omega
    · intro clock
      rw [show clock + (1 + restCount) = (clock + restCount) + 1 by omega, firstRun]
      simpa only [nextFfi] using restRun clock

end InitECandidate.Runtime.LabToTarget
#print axioms InitECandidate.Runtime.LabToTarget.weightedMixedTrace_bounded
