import InitECandidate.Runtime.EncoderBudget
import InitECandidate.Runtime.EncoderLoc

namespace InitECandidate.Runtime
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.Semantics.TargetProps

/-- The concrete address-load encoder has an exact two-instruction witness. -/
theorem loc_encoder_budget (r : Nat) (offset : BitVec 64)
    (before after : AsmState 64) (ms : riscv_state)
    (step : asmStep riscvTarget.config before (.loc r offset) after)
    (related : targetStateRel riscvTarget before ms) :
    ∃ n, n + 1 ≤ 2 ∧ encoderStepAt riscvTarget before (.loc r offset) after ms n := by
  obtain ⟨n, count, run⟩ := Encoder.loc_encoder_correct_two_steps r offset before after ms
    ⟨step, related⟩
  exact ⟨n, Nat.le_of_eq count, run⟩

/-- Concrete quantitative compiler step, through the authoritative target
clocked evaluator and its dispatcher. Every original guard is retained. -/
theorem loc_step_evaluator_bounded {σ : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection)
    (before : AsmState 64) (ms : riscv_state) (io : HolFfiState σ)
    (r : Nat) (offset : BitVec 64)
    (target : mc.target = riscvTarget)
    (h : encoderCorrect mc.target ∧ mc.progAddresses = before.memDomain ∧
      ffiEntryPcsDisjoint mc before (mc.target.config.encode (.loc r offset)).length ∧
      interferenceOk mc.nextInterfer (mc.target.proj before.memDomain) ∧
      asmStep mc.target.config before (.loc r offset)
        (asmUpd (.loc r offset)
          (before.pc + BitVec.ofNat 64 (mc.target.config.encode (.loc r offset)).length) before) ∧
      targetStateRel mc.target before ms) :
    ∃ count post, count ≤ 2 ∧
      (∀ clock, evaluateTargetHOL mc io (clock + count) ms =
        evaluateTargetHOL (shiftInterfer count mc) io clock post) ∧
      targetStateRel mc.target
        (asmUpd (.loc r offset)
          (before.pc + BitVec.ofNat 64 (mc.target.config.encode (.loc r offset)).length) before) post := by
  have quantitative : ∃ n, n + 1 ≤ 2 ∧ encoderStepAt mc.target before (.loc r offset)
      (asmUpd (.loc r offset)
        (before.pc + BitVec.ofNat 64 (mc.target.config.encode (.loc r offset)).length) before) ms n := by
    rw [target]
    apply loc_encoder_budget
    · simpa only [target] using h.2.2.2.2.1
    · simpa only [target] using h.2.2.2.2.2
  obtain ⟨count, post, bound, run⟩ := asmStepImpEvaluate_bounded mc before ms io
    (.loc r offset) h 2 quantitative
  exact ⟨count, post, bound, fun clock => (run clock).1, (run 0).2.2.1⟩

end InitECandidate.Runtime

#print axioms InitECandidate.Runtime.loc_step_evaluator_bounded
