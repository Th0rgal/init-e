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

theorem extraction_of_instruction {F : Type} {state next post : LabSem.State 64 Config F}
    {outcome : HolOutcome} (trace : InstructionTrace state next 1)
    (sameCode : next.code = state.code) (evaluated : evaluate next = (.halt outcome, post)) :
    ExtractionStep state post outcome := by
  refine Or.inr ⟨next, MixedTrace.ordinary state next next 1 0 trace (.nil next), ?_, sameCode, evaluated⟩
  have source := (instructionTrace_source trace).2
  omega

theorem clock_of_halt_evaluation {F : Type} {state post : LabSem.State 64 Config F}
    {outcome : HolOutcome} (evaluated : evaluate state = (.halt outcome, post)) : state.clock ≠ 0 := by
  intro zero
  rw [evaluate] at evaluated
  simp [zero] at evaluated

theorem extract_jump_step {F : Type} (state post : LabSem.State 64 Config F)
    (outcome : HolOutcome) (label : Lab) (w : BitVec 64) (bytes : List (BitVec 8)) (n : Nat)
    (fetch : asmFetch state = some (.labAsm (.jump label) w bytes n))
    (evaluated : evaluate state = (.halt outcome, post)) : ExtractionStep state post outcome := by
  have clock := clock_of_halt_evaluation evaluated
  rw [evaluate] at evaluated
  simp only [clock, ↓reduceIte, fetch] at evaluated
  cases destination : getPcValue label state with
  | none => simp only [destination] at evaluated; cases (Prod.mk.inj evaluated).1
  | some pc =>
    simp only [destination] at evaluated
    exact extraction_of_instruction
      (InstructionTrace.jump state _ label pc w bytes n 0 clock fetch destination (.nil _)) rfl evaluated

theorem extract_jumpReg_step {F : Type} (state post : LabSem.State 64 Config F)
    (outcome : HolOutcome) (r : Nat) (bytes : List (BitVec 8)) (n : Nat)
    (fetch : asmFetch state = some (.asm (.asmi (.jumpReg r)) bytes n))
    (evaluated : evaluate state = (.halt outcome, post)) : ExtractionStep state post outcome := by
  have clock := clock_of_halt_evaluation evaluated
  rw [evaluate] at evaluated
  simp only [clock, ↓reduceIte, fetch] at evaluated
  cases register : state.regs r with
  | word value => simp only [register] at evaluated; cases (Prod.mk.inj evaluated).1
  | loc n1 n2 =>
    simp only [register] at evaluated
    cases destination : locToPc n1 n2 state.code with
    | none => simp only [destination] at evaluated; cases (Prod.mk.inj evaluated).1
    | some pc =>
      simp only [destination] at evaluated
      exact extraction_of_instruction
        (InstructionTrace.jumpReg state _ r n1 n2 pc bytes n 0 clock fetch register destination (.nil _)) rfl evaluated

theorem extract_locValue_step {F : Type} (state post : LabSem.State 64 Config F)
    (outcome : HolOutcome) (r : Nat) (label : Lab) (w : BitVec 64) (bytes : List (BitVec 8)) (n : Nat)
    (fetch : asmFetch state = some (.labAsm (.locValue r label) w bytes n))
    (evaluated : evaluate state = (.halt outcome, post)) : ExtractionStep state post outcome := by
  have clock := clock_of_halt_evaluation evaluated
  rw [evaluate] at evaluated
  simp only [clock, ↓reduceIte, fetch] at evaluated
  cases destination : getPcValue label state with
  | none => simp only [destination, ↓reduceIte] at evaluated; cases (Prod.mk.inj evaluated).1
  | some pc =>
    simp only [destination, reduceCtorEq, ↓reduceIte] at evaluated
    exact extraction_of_instruction
      (InstructionTrace.locValue state _ r label pc w bytes n 0 clock fetch destination (.nil _)) rfl evaluated

theorem extract_branch_step {F : Type} (state post : LabSem.State 64 Config F)
    (outcome : HolOutcome) (cmp : HolCmp) (r : Nat) (operand : HolRegImm 64)
    (label : Lab) (w : BitVec 64) (bytes : List (BitVec 8)) (n : Nat)
    (fetch : asmFetch state = some (.labAsm (.jumpCmp cmp r operand label) w bytes n))
    (evaluated : evaluate state = (.halt outcome, post)) : ExtractionStep state post outcome := by
  have clock := clock_of_halt_evaluation evaluated
  rw [evaluate] at evaluated
  simp only [clock, ↓reduceIte, fetch] at evaluated
  cases chosen : wordSemWordCmp cmp (state.regs r) (LabSem.regImm operand state) with
  | none => simp only [chosen] at evaluated; cases (Prod.mk.inj evaluated).1
  | some b =>
    cases b with
    | false =>
      simp only [chosen] at evaluated
      exact extraction_of_instruction
        (InstructionTrace.branchFallthrough state _ cmp r operand label w bytes n 0 clock fetch chosen (.nil _)) rfl evaluated
    | true =>
      simp only [chosen] at evaluated
      cases destination : getPcValue label state with
      | none => simp only [destination] at evaluated; cases (Prod.mk.inj evaluated).1
      | some pc =>
        simp only [destination] at evaluated
        exact extraction_of_instruction
          (InstructionTrace.branchTaken state _ cmp r operand label pc w bytes n 0 clock fetch chosen destination (.nil _)) rfl evaluated

/-- Syntax supported by the bounded simulation. Dynamic installation,
shared memory and code-buffer writes require separate compiler invariants. -/
inductive SupportedLine : LabLineHOL 64 → Prop
  | inst (i : HolInst 64) (bytes : List (BitVec 8)) (n : Nat) :
      SupportedLine (.asm (.asmi (.inst i)) bytes n)
  | jumpReg (r : Nat) (bytes : List (BitVec 8)) (n : Nat) :
      SupportedLine (.asm (.asmi (.jumpReg r)) bytes n)
  | halt (w : BitVec 64) (bytes : List (BitVec 8)) (n : Nat) : SupportedLine (.labAsm .halt w bytes n)
  | jump (label : Lab) (w : BitVec 64) (bytes : List (BitVec 8)) (n : Nat) :
      SupportedLine (.labAsm (.jump label) w bytes n)
  | branch (cmp : HolCmp) (r : Nat) (operand : HolRegImm 64) (label : Lab)
      (w : BitVec 64) (bytes : List (BitVec 8)) (n : Nat) :
      SupportedLine (.labAsm (.jumpCmp cmp r operand label) w bytes n)
  | locValue (r : Nat) (label : Lab) (w : BitVec 64) (bytes : List (BitVec 8)) (n : Nat) :
      SupportedLine (.labAsm (.locValue r label) w bytes n)
  | ffi (name : MlString) (w : BitVec 64) (bytes : List (BitVec 8)) (n : Nat) :
      SupportedLine (.labAsm (.callFFI name) w bytes n)

def SupportedCode (code : LabProgHOL 64) : Prop :=
  ∀ pc line, asmFetchAux pc code = some line → SupportedLine line

theorem extract_supported_step {F : Type} (state post : LabSem.State 64 Config F)
    (outcome : HolOutcome) (supported : SupportedCode state.code)
    (evaluated : evaluate state = (.halt outcome, post)) : ExtractionStep state post outcome := by
  cases fetch : asmFetch state with
  | none =>
    have clock := clock_of_halt_evaluation evaluated
    rw [evaluate] at evaluated
    simp only [clock, ↓reduceIte, fetch] at evaluated
    cases (Prod.mk.inj evaluated).1
  | some line =>
    have allowed := supported state.pc line (by simpa only [asmFetch] using fetch)
    cases allowed with
    | inst i bytes n => exact extract_inst_step state post outcome i bytes n fetch evaluated
    | jumpReg r bytes n => exact extract_jumpReg_step state post outcome r bytes n fetch evaluated
    | halt w bytes n => exact Or.inl (terminal_of_halt_fetch state post outcome w bytes n fetch evaluated)
    | jump label w bytes n => exact extract_jump_step state post outcome label w bytes n fetch evaluated
    | branch cmp r operand label w bytes n =>
      exact extract_branch_step state post outcome cmp r operand label w bytes n fetch evaluated
    | locValue r label w bytes n => exact extract_locValue_step state post outcome r label w bytes n fetch evaluated
    | ffi name w bytes n => exact extract_ffi_step state post outcome name w bytes n fetch evaluated

theorem mixedTrace_trans {F : Type} {a b c : LabSem.State 64 Config F} {m n : Nat}
    (first : MixedTrace a b m) (second : MixedTrace b c n) : MixedTrace a c (m + n) := by
  induction first with
  | nil state => simpa only [Nat.zero_add] using second
  | ordinary start middle final length restLength segment rest ih =>
    simpa only [Nat.add_assoc] using MixedTrace.ordinary start middle c length (restLength + n) segment (ih second)
  | ffi state final name w bytes k len start len2 start2 conf bytes2 n1 n2 pc newFfi newBytes
      length clock fetch hlen hptr hlen2 hptr2 read1 read2 link destination call rest ih =>
    have composed := MixedTrace.ffi state c name w bytes k len start len2 start2 conf bytes2 n1 n2 pc
      newFfi newBytes (length + n) clock fetch hlen hptr hlen2 hptr2 read1 read2 link destination call (ih second)
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using composed

/-- Successful evaluation of supported code supplies its own complete trace
and terminal witness. Neither a runtime trace nor its length is assumed. -/
theorem extract_supported_trace {F : Type} (state post : LabSem.State 64 Config F)
    (outcome : HolOutcome) (supported : SupportedCode state.code)
    (evaluated : evaluate state = (.halt outcome, post)) :
    ∃ length, MixedTrace state post length ∧ Terminal post outcome := by
  rcases extract_supported_step state post outcome supported evaluated with done | ⟨next, step, smaller, sameCode, nextEval⟩
  · obtain ⟨terminal, rfl⟩ := done
    exact ⟨0, .nil post, terminal⟩
  · obtain ⟨length, rest, terminal⟩ := extract_supported_trace next post outcome (by rwa [sameCode]) nextEval
    exact ⟨1 + length, mixedTrace_trans step rest, terminal⟩
termination_by state.clock

/-- Quantitative label-to-native termination for supported code. The runtime
trace is derived from evaluation; its clock supplies the final linear bound. -/
theorem supported_evaluation_native_bound {F : Type} (state post : LabSem.State 64 Config F)
    (outcome : HolOutcome) (supported : SupportedCode state.code)
    (evaluated : evaluate state = (.halt outcome, post))
    (mc : MachineConfig 64 riscv_state RiscVProjection) (code : LabProgHOL 64)
    (labs : Spt (Spt Nat)) (p : BitVec 64) (asm : AsmState 64) (machine : riscv_state)
    (target : mc.target = riscvTarget) (encoder : encoderCorrect mc.target)
    (related : stateRel (mc, code, labs, p) state asm machine) (tie : oracleTie mc machine state) :
    ∃ count native, count ≤ (labStepCeiling code + 1) * state.clock ∧
      evaluateTargetHOL mc state.ffi count machine = (.halt outcome, native, post.ffi) := by
  obtain ⟨length, trace, terminal⟩ := extract_supported_trace state post outcome supported evaluated
  obtain ⟨firstCount, middle, middleAsm, finalConfig, firstBound, finalTarget,
      finalEncoder, firstRun, middleRel, middleTie⟩ :=
    mixedTrace_bounded trace mc code labs p asm machine target encoder related tie
  obtain ⟨lastCount, native, lastBound, lastRun⟩ :=
    terminal_native terminal finalConfig code labs p middleAsm middle finalTarget finalEncoder middleRel
  refine ⟨lastCount + firstCount, native, ?_, ?_⟩
  · have sourceClock := (mixedTrace_source trace).2
    have positive := terminal_clock terminal
    have lengthBound : length + 1 ≤ state.clock := by omega
    have ceiling : 17 ≤ labStepCeiling code + 1 := by unfold labStepCeiling; omega
    have multiplied := Nat.mul_le_mul_left (labStepCeiling code + 1) lengthBound
    rw [Nat.mul_add, Nat.mul_one] at multiplied
    omega
  · rw [firstRun, lastRun]

end InitECandidate.Runtime.LabToTarget
#print axioms InitECandidate.Runtime.LabToTarget.extract_ffi_step

#print axioms InitECandidate.Runtime.LabToTarget.extract_inst_step

#print axioms InitECandidate.Runtime.LabToTarget.extract_branch_step

#print axioms InitECandidate.Runtime.LabToTarget.extract_supported_trace

#print axioms InitECandidate.Runtime.LabToTarget.supported_evaluation_native_bound
