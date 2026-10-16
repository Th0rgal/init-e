import InitECandidate.Runtime.EncoderBudget
import InitECandidate.Runtime.EncoderMemory

namespace InitECandidate.Runtime
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.Semantics.TargetProps

/-- Every supported memory operation has a one-native-instruction witness. -/
theorem memory_encoder_budget (op : HolMemop) (r base : Nat) (offset : BitVec 64)
    (before after : AsmState 64) (ms : riscv_state)
    (step : asmStep riscvTarget.config before (.inst (.mem op r (.addr base offset))) after)
    (related : targetStateRel riscvTarget before ms) :
    ∃ n, n + 1 ≤ 1 ∧ encoderStepAt riscvTarget before (.inst (.mem op r (.addr base offset))) after ms n := by
  obtain ⟨n, count, run⟩ := Encoder.mem_encoder_correct_one_step op r base offset before after ms
    ⟨step, related⟩
  exact ⟨n, Nat.le_of_eq count, run⟩

/-- Concrete quantitative compiler step, through the authoritative target
clocked evaluator and its dispatcher. Every original guard is retained. -/
theorem memory_step_evaluator_bounded {σ : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection)
    (before : AsmState 64) (ms : riscv_state) (io : HolFfiState σ)
    (op : HolMemop) (r base : Nat) (offset : BitVec 64)
    (target : mc.target = riscvTarget)
    (h : encoderCorrect mc.target ∧ mc.progAddresses = before.memDomain ∧
      ffiEntryPcsDisjoint mc before (mc.target.config.encode (.inst (.mem op r (.addr base offset)))).length ∧
      interferenceOk mc.nextInterfer (mc.target.proj before.memDomain) ∧
      asmStep mc.target.config before (.inst (.mem op r (.addr base offset)))
        (asmUpd (.inst (.mem op r (.addr base offset)))
          (before.pc + BitVec.ofNat 64 (mc.target.config.encode (.inst (.mem op r (.addr base offset)))).length) before) ∧
      targetStateRel mc.target before ms) :
    ∃ count post, count ≤ 1 ∧
      (∀ clock, evaluateTargetHOL mc io (clock + count) ms =
        evaluateTargetHOL (shiftInterfer count mc) io clock post) ∧
      targetStateRel mc.target
        (asmUpd (.inst (.mem op r (.addr base offset)))
          (before.pc + BitVec.ofNat 64 (mc.target.config.encode (.inst (.mem op r (.addr base offset)))).length) before) post := by
  have quantitative : ∃ n, n + 1 ≤ 1 ∧ encoderStepAt mc.target before (.inst (.mem op r (.addr base offset)))
      (asmUpd (.inst (.mem op r (.addr base offset)))
        (before.pc + BitVec.ofNat 64 (mc.target.config.encode (.inst (.mem op r (.addr base offset)))).length) before) ms n := by
    rw [target]
    apply memory_encoder_budget
    · simpa only [target] using h.2.2.2.2.1
    · simpa only [target] using h.2.2.2.2.2
  obtain ⟨count, post, bound, run⟩ := asmStepImpEvaluate_bounded mc before ms io
    (.inst (.mem op r (.addr base offset))) h 1 quantitative
  exact ⟨count, post, bound, fun clock => (run clock).1, (run 0).2.2.1⟩

end InitECandidate.Runtime

#print axioms InitECandidate.Runtime.memory_step_evaluator_bounded
