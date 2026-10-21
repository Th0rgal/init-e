import InitECandidate.Runtime.LabInstructionLocalCost
import InitECandidate.Runtime.AsmLocalCost
import Flapjack.RiscV.CorrectnessEncoding.Length
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.RiscV.TargetProof

/-- Even the encoder's fallback emits one complete four-byte instruction. -/
theorem native_instruction_encoding_min (instruction : HolInst 64) :
    4 ≤ (riscvTarget.config.encode (.inst instruction)).length := by
  have encoded := riscv_encoding (.inst instruction)
  have positive := List.length_pos_iff.mpr encoded.2
  change 4 ≤ (riscvEnc (.inst instruction)).length
  omega

/-- Only bytes beyond the instruction's own encoding contribute padding. -/
theorem instructionWork_padding_bound (code : LabProgHOL 64) (pc gap : Nat)
    (instruction : HolInst 64)
    (span : (posVal (pc+1) 0 code - posVal pc 0 code)/4 ≤ gap) :
    LabToTarget.LocalCost.instructionWork code pc instruction ≤ instLocalCost instruction + (gap-1) := by
  have encoded := native_instruction_encoding_min instruction
  unfold LabToTarget.LocalCost.instructionWork
  have padding : (posVal (pc+1) 0 code - posVal pc 0 code -
      (riscvTarget.config.encode (.inst instruction)).length)/4 ≤ gap-1 := by omega
  exact Nat.add_le_add_left padding _

/-- Constant encoding and padding share one local span rather than paying
independent maxima. The bound also covers spans shorter than the encoding. -/
theorem constantInstructionWork_max (code : LabProgHOL 64) (pc gap rd : Nat)
    (value : BitVec 64)
    (span : (posVal (pc+1) 0 code - posVal pc 0 code)/4 ≤ gap) :
    LabToTarget.LocalCost.instructionWork code pc (.const rd value) ≤
      max (instLocalCost (.const rd value)) gap := by
  have encoding := riscvEnc_length_eq (.inst (.const rd value))
  change (riscvTarget.config.encode (.inst (.const rd value))).length =
    4 * (riscvAst (.inst (.const rd value))).length at encoding
  unfold LabToTarget.LocalCost.instructionWork
  simp only [instLocalCost]
  rw [encoding]
  omega

#print axioms native_instruction_encoding_min
#print axioms instructionWork_padding_bound
#print axioms constantInstructionWork_max
end InitECandidate.Runtime.StackToLab
