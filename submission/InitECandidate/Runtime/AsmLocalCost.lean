import InitECandidate.Runtime.UniformAsmBudget
namespace InitECandidate.Runtime
open Flapjack Flapjack.RiscV.L3
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.AsmSem
open Flapjack.Compiler.Encoders.AsmProps Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.Semantics.TargetProps
open InitECandidate.Proofs.BootstrapSteps InitECandidate.Proofs.BootstrapCopy
open InitECandidate.Proofs.BootstrapAsmComposition

/-- Costs of actual emitted native expansions, independent of ROM size. -/
def instLocalCost : HolInst 64 → Nat
  | .skip => 1
  | .const rd value => (riscvAst (.inst (.const rd value))).length
  | .arith (.binop _ _ _ _) | .arith (.div _ _ _) | .mem _ _ _ => 1
  | .arith (.shift _ _ _ _) => 5
  | _ => 16

def asmLocalCost : HolAsm 64 → Nat
  | .inst instruction => instLocalCost instruction
  | .jump _ | .call _ | .loc _ _ => 2
  | .jumpCmp _ _ _ _ => 3
  | .jumpReg _ => 1

theorem inst_encoder_local_budget (instruction : HolInst 64)
    (before after : AsmState 64) (ms : riscv_state)
    (step : asmStep riscvTarget.config before (.inst instruction) after)
    (related : targetStateRel riscvTarget before ms) :
    ∃ n, n + 1 ≤ instLocalCost instruction ∧
      encoderStepAt riscvTarget before (.inst instruction) after ms n := by
  cases instruction with
  | skip =>
    obtain ⟨n, count, run⟩ := Encoder.skip_one_step before after ms ⟨step, related⟩
    exact ⟨n, by simpa only [instLocalCost] using Nat.le_of_eq count, run⟩
  | const rd value =>
    obtain ⟨n, count, run⟩ := Encoder.const_encoder_correct_count rd value before after ms ⟨step, related⟩
    exact ⟨n, by simpa only [instLocalCost] using Nat.le_of_eq count, run⟩
  | mem op rd address =>
    cases address with
    | addr base offset => exact memory_encoder_budget op rd base offset before after ms step related
  | arith operation =>
    cases operation with
    | binop op rd rs operand => exact binop_encoder_budget op rd rs operand before after ms step related
    | shift op rd rs operand => exact all_shift_encoder_budget op rd rs operand before after ms step related
    | div rd rs rt => exact div_encoder_budget rd rs rt before after ms step related
    | _ => exact arith_encoder_budget _ before after ms step related

theorem asm_encoder_local_budget (instruction : HolAsm 64)
    (before after : AsmState 64) (ms : riscv_state)
    (step : asmStep riscvTarget.config before instruction after)
    (related : targetStateRel riscvTarget before ms) :
    ∃ n, n + 1 ≤ asmLocalCost instruction ∧
      encoderStepAt riscvTarget before instruction after ms n := by
  cases instruction with
  | inst value => exact inst_encoder_local_budget value before after ms step related
  | jump offset => exact jump_encoder_budget offset before after ms step related
  | jumpCmp cmp r right offset => exact branch_encoder_budget cmp r right offset before after ms step related
  | call offset => exact call_encoder_budget offset before after ms step related
  | jumpReg r => exact jumpReg_encoder_budget r before after ms step related
  | loc r offset => exact loc_encoder_budget r offset before after ms step related

/-- Per-instruction coefficients apply to the actual checked execution trace. -/
theorem checked_trace_local_budgets (code : List (HolAsm 64)) (state : AsmState 64)
    (checks : Checked code state) : TraceBudgets asmLocalCost code state := by
  induction code generalizing state with
  | nil => trivial
  | cons instruction rest ih =>
    constructor
    · intro machine related
      apply asm_encoder_local_budget instruction state (after state instruction) machine
      · simpa only [riscvTarget, riscvConfig_encode, after] using checks.1
      · exact related
    · exact ih (after state instruction) checks.2

theorem checked_trace_local_bound {F : Type}
    (mc : MachineConfig 64 riscv_state RiscVProjection) (target : mc.target = riscvTarget)
    (identity : mc.nextInterfer = fun _ state => state)
    (code : List (HolAsm 64)) (state : AsmState 64)
    (checks : Checked code state) (guards : EvaluatorGuards mc code state)
    (machine : riscv_state) (io : HolFfiState F)
    (related : targetStateRel riscvTarget state machine) :
    ∃ count post, count ≤ traceCost asmLocalCost code ∧
      (∀ clock, evaluateTargetHOL mc io (count + clock) machine =
        evaluateTargetHOL mc io clock post) ∧
      targetStateRel riscvTarget (run code state) post :=
  checked_trace_evaluator_bounded mc target identity asmLocalCost code state checks guards
    (checked_trace_local_budgets code state checks) machine io related

#print axioms checked_trace_local_bound
#print axioms asm_encoder_local_budget
end InitECandidate.Runtime
