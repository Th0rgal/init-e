import InitECandidate.Runtime.ArithBudget
import InitECandidate.Runtime.MemoryBudget
import InitECandidate.Runtime.EncoderConst
import InitECandidate.Runtime.EncoderSkip

namespace InitECandidate.Runtime
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.Semantics.TargetProps

theorem const_native_length_le (rd : Nat) (value : BitVec 64) :
    (riscvAst (.inst (.const rd value))).length ≤ 6 := by
  simp only [riscvAst]
  repeat' split
  all_goals simp [riscvConst32]
  all_goals repeat' split
  all_goals simp_all

/-- All ordinary assembly instructions have a uniform native-step ceiling. -/
theorem inst_encoder_budget (instruction : HolInst 64)
    (before after : AsmState 64) (ms : riscv_state)
    (step : asmStep riscvTarget.config before (.inst instruction) after)
    (related : targetStateRel riscvTarget before ms) :
    ∃ n, n + 1 ≤ 16 ∧ encoderStepAt riscvTarget before (.inst instruction) after ms n := by
  cases instruction with
  | skip =>
    obtain ⟨n, bound, run⟩ := Encoder.skip_one_step before after ms ⟨step, related⟩
    exact ⟨n, by omega, run⟩
  | const rd value =>
    obtain ⟨n, count, run⟩ := Encoder.const_encoder_correct_count rd value before after ms ⟨step, related⟩
    have bound := const_native_length_le rd value
    exact ⟨n, by omega, run⟩
  | arith operation => exact arith_encoder_budget operation before after ms step related
  | mem operation rd address =>
    cases address with
    | addr base offset =>
      obtain ⟨n, bound, run⟩ := memory_encoder_budget operation rd base offset before after ms step related
      exact ⟨n, by omega, run⟩

theorem inst_step_evaluator_bounded {σ : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection)
    (before : AsmState 64) (ms : riscv_state) (io : HolFfiState σ)
    (instruction : HolInst 64)
    (target : mc.target = riscvTarget)
    (h : encoderCorrect mc.target ∧ mc.progAddresses = before.memDomain ∧
      ffiEntryPcsDisjoint mc before (mc.target.config.encode (.inst instruction)).length ∧
      interferenceOk mc.nextInterfer (mc.target.proj before.memDomain) ∧
      asmStep mc.target.config before (.inst instruction)
        (asmUpd (.inst instruction)
          (before.pc + BitVec.ofNat 64 (mc.target.config.encode (.inst instruction)).length) before) ∧
      targetStateRel mc.target before ms) :
    ∃ count post, count ≤ 16 ∧
      (∀ clock, evaluateTargetHOL mc io (clock + count) ms =
        evaluateTargetHOL (shiftInterfer count mc) io clock post) ∧
      targetStateRel mc.target
        (asmUpd (.inst instruction)
          (before.pc + BitVec.ofNat 64 (mc.target.config.encode (.inst instruction)).length) before) post := by
  have quantitative : ∃ n, n + 1 ≤ 16 ∧ encoderStepAt mc.target before (.inst instruction)
      (asmUpd (.inst instruction)
        (before.pc + BitVec.ofNat 64 (mc.target.config.encode (.inst instruction)).length) before) ms n := by
    rw [target]
    apply inst_encoder_budget
    · simpa only [target] using h.2.2.2.2.1
    · simpa only [target] using h.2.2.2.2.2
  obtain ⟨count, post, bound, run⟩ := asmStepImpEvaluate_bounded mc before ms io
    (.inst instruction) h 16 quantitative
  exact ⟨count, post, bound, fun clock => (run clock).1, (run 0).2.2.1⟩

end InitECandidate.Runtime
#print axioms InitECandidate.Runtime.inst_step_evaluator_bounded
