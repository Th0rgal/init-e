import InitECandidate.Runtime.LabMixedTrace

namespace InitECandidate.Runtime.LabToTarget
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Basis.Pure.MlString

/-- Concrete successful stopping cases of the supported label evaluator. -/
inductive Terminal {F : Type} : LabSem.State 64 Config F → HolOutcome → Prop
  | halt (state : LabSem.State 64 Config F) (w value : BitVec 64)
      (bytes : List (BitVec 8)) (n : Nat)
      (clock : state.clock ≠ 0)
      (fetch : asmFetch state = some (.labAsm .halt w bytes n))
      (result : state.regs state.ptrReg = .word value) :
      Terminal state (if value = 0 then .success else .resourceLimitHit)
  | ffi (state : LabSem.State 64 Config F) (name : MlString) (w : BitVec 64)
      (bytes : List (BitVec 8)) (n : Nat)
      (len start len2 start2 : BitVec 64) (conf bytes2 : List (BitVec 8))
      (n1 n2 newPc : Nat) (event : HolFinalEvent)
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
      (call : callFFIHOL state.ffi (.extCall name) conf bytes2 = .final event)
      : Terminal state (.ffiOutcome event)

theorem terminal_clock {F : Type} {state : LabSem.State 64 Config F} {outcome : HolOutcome}
    (terminal : Terminal state outcome) : state.clock ≠ 0 := by
  cases terminal <;> assumption

theorem terminal_source {F : Type} {state : LabSem.State 64 Config F} {outcome : HolOutcome}
    (terminal : Terminal state outcome) : evaluate state = (.halt outcome, state) := by
  cases terminal with
  | halt w value bytes n clock fetch result =>
    rw [evaluate]
    by_cases zero : value = (0#64) <;> simp [clock, fetch, result, zero]
  | ffi name w bytes n len start len2 start2 conf bytes2 n1 n2 newPc event clock fetch
      hlen hptr hlen2 hptr2 read1 read2 link destination call =>
    rw [evaluate]
    simp only [clock, ↓reduceIte, fetch, hlen, hptr, hlen2, hptr2, link,
      read1, read2, destination, call]

theorem terminal_native {F : Type} {state : LabSem.State 64 Config F} {outcome : HolOutcome}
    (terminal : Terminal state outcome)
    (mc : MachineConfig 64 riscv_state RiscVProjection) (code : LabProgHOL 64)
    (labs : Spt (Spt Nat)) (p : BitVec 64) (asm : AsmState 64) (machine : riscv_state)
    (target : mc.target = riscvTarget) (encoder : encoderCorrect mc.target)
    (related : stateRel (mc, code, labs, p) state asm machine) :
    ∃ count post, count ≤ 17 ∧ evaluateTargetHOL mc state.ffi count machine =
      (.halt outcome, post, state.ffi) := by
  cases terminal with
  | halt w value bytes n clock fetch result =>
    exact fetched_halt_bounded state w value mc code labs p asm machine bytes n target fetch result encoder related
  | ffi name w bytes n len start len2 start2 conf bytes2 n1 n2 newPc event clock fetch
      hlen hptr hlen2 hptr2 read1 read2 link destination call =>
    exact fetched_ffi_final_bounded state name w mc code labs p asm machine bytes n len start len2 start2
      conf bytes2 target fetch hlen hptr hlen2 hptr2 read1 read2 encoder related event call

/-- Extract the halt terminal witness from the evaluator result itself. -/
theorem terminal_of_halt_fetch {F : Type} (state post : LabSem.State 64 Config F)
    (outcome : HolOutcome) (w : BitVec 64) (bytes : List (BitVec 8)) (n : Nat)
    (fetch : asmFetch state = some (.labAsm .halt w bytes n))
    (evaluated : evaluate state = (.halt outcome, post)) :
    Terminal state outcome ∧ post = state := by
  have clock : state.clock ≠ 0 := by
    intro zero
    rw [evaluate] at evaluated
    simp [zero] at evaluated
  cases reg : state.regs state.ptrReg with
  | loc a b =>
    rw [evaluate] at evaluated
    simp [clock, fetch, reg] at evaluated
  | word value =>
    have source := terminal_source (Terminal.halt state w value bytes n clock fetch reg)
    rw [source] at evaluated
    have pieces := Prod.mk.inj evaluated
    have result : outcome = (if value = 0 then .success else .resourceLimitHit) := by
      exact (MachineResult.halt.inj pieces.1).symm
    rw [result]
    exact ⟨Terminal.halt state w value bytes n clock fetch reg, pieces.2.symm⟩

end InitECandidate.Runtime.LabToTarget
#print axioms InitECandidate.Runtime.LabToTarget.terminal_native

#print axioms InitECandidate.Runtime.LabToTarget.terminal_of_halt_fetch
