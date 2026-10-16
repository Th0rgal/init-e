import InitECandidate.Runtime.LabTerminal

namespace InitECandidate.Runtime.LabToTarget
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Backend.Semantics.TargetProps
open Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Basis.Pure.MlString

/-- The recursive extraction alternatives retain the actual source evaluator
result, code identity and strict clock decrease. No trace is assumed. -/
def ExtractionStep {F : Type} (state post : LabSem.State 64 Config F) (outcome : HolOutcome) : Prop :=
  (Terminal state outcome ∧ post = state) ∨
    ∃ next, MixedTrace state next 1 ∧ next.clock < state.clock ∧ next.code = state.code ∧
      evaluate next = (.halt outcome, post)

/-- Extract all FFI operands, reads, destination and call result directly
from a successful evaluation of a fetched FFI line. -/
theorem extract_ffi_step {F : Type} (state post : LabSem.State 64 Config F)
    (outcome : HolOutcome) (name : MlString) (w : BitVec 64)
    (bytes : List (BitVec 8)) (n : Nat)
    (fetch : asmFetch state = some (.labAsm (.callFFI name) w bytes n))
    (evaluated : evaluate state = (.halt outcome, post)) : ExtractionStep state post outcome := by
  have clock : state.clock ≠ 0 := by
    intro zero
    rw [evaluate] at evaluated
    simp [zero] at evaluated
  rw [evaluate] at evaluated
  simp only [clock, ↓reduceIte, fetch] at evaluated
  split at evaluated
  rotate_left
  · cases (Prod.mk.inj evaluated).1
  rename_i len start len2 start2 n1 n2 hlen hptr hlen2 hptr2 hlink
  split at evaluated
  rotate_left
  · cases (Prod.mk.inj evaluated).1
  rename_i conf bytes2 pc read1 read2 destination
  cases call : callFFIHOL state.ffi (.extCall name) conf bytes2 with
  | final event =>
    rw [call] at evaluated
    have pieces := Prod.mk.inj evaluated
    have result := MachineResult.halt.inj pieces.1
    cases result
    exact Or.inl ⟨Terminal.ffi state name w bytes n len start len2 start2 conf bytes2 n1 n2 pc event
      clock fetch hlen hptr hlen2 hptr2 read1 read2 hlink destination call, pieces.2.symm⟩
  | ret newFfi newBytes =>
    rw [call] at evaluated
    let next := ffiReturnedSource state name start2 newBytes pc newFfi
    refine Or.inr ⟨next, ?_, ?_, rfl, evaluated⟩
    · exact MixedTrace.ffi state next name w bytes n len start len2 start2 conf bytes2 n1 n2 pc
        newFfi newBytes 0 clock fetch hlen hptr hlen2 hptr2 read1 read2 hlink destination call (.nil next)
    · change state.clock - 1 < state.clock
      omega

theorem extract_inst_step {F : Type} (state post : LabSem.State 64 Config F)
    (outcome : HolOutcome) (i : HolInst 64) (bytes : List (BitVec 8)) (n : Nat)
    (fetch : asmFetch state = some (.asm (.asmi (.inst i)) bytes n))
    (evaluated : evaluate state = (.halt outcome, post)) : ExtractionStep state post outcome := by
  have clock : state.clock ≠ 0 := by
    intro zero
    rw [evaluate] at evaluated
    simp [zero] at evaluated
  rw [evaluate] at evaluated
  simp only [clock, ↓reduceIte, fetch] at evaluated
  by_cases failed : (asmInst i state).failed = true
  · simp only [failed, ↓reduceIte] at evaluated
    cases (Prod.mk.inj evaluated).1
  · simp only [failed, Bool.false_eq_true, ↓reduceIte] at evaluated
    let next := incPc (decClock (asmInst i state))
    refine Or.inr ⟨next, ?_, ?_, ?_, evaluated⟩
    · exact MixedTrace.ordinary state next next 1 0
        (InstructionTrace.step state next i bytes n 0 clock fetch failed (.nil next)) (.nil next)
    · obtain ⟨_, _, sameClock, _⟩ := asmInstConsts i state
      change (asmInst i state).clock - 1 < state.clock
      rw [sameClock]
      omega
    · obtain ⟨_, sameCode, _⟩ := asmInstConsts i state
      exact sameCode

end InitECandidate.Runtime.LabToTarget
#print axioms InitECandidate.Runtime.LabToTarget.extract_ffi_step

#print axioms InitECandidate.Runtime.LabToTarget.extract_inst_step
