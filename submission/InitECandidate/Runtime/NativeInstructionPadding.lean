import InitECandidate.Runtime.StackNativeLocalPrice
import InitECandidate.Runtime.InstBudget
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

/-- The local span already contains the encoded instruction. Only the
remaining bytes are padding, so a six-word span permits at most five padding
instructions, not six extra ones. -/
theorem instructionWork_padding_five (code : LabProgHOL 64)
    (bounded : encodedLineWords code ≤ 6) (pc : Nat) (instruction : HolInst 64) :
    LabToTarget.LocalCost.instructionWork code pc instruction ≤ instLocalCost instruction + 5 := by
  have span := (encodedLineWords_bound code pc).trans bounded
  have encoded := native_instruction_encoding_min instruction
  unfold LabToTarget.LocalCost.instructionWork
  have padding : (posVal (pc+1) 0 code - posVal pc 0 code -
      (riscvTarget.config.encode (.inst instruction)).length) / 4 ≤ 5 := by omega
  exact Nat.add_le_add_left padding _

/-- Literal encoding and following padding share the same six-word span.
Their costs must not be added as two independent worst cases. -/
theorem constantInstructionWork_six (code : LabProgHOL 64)
    (bounded : encodedLineWords code ≤ 6) (pc rd : Nat) (value : BitVec 64) :
    LabToTarget.LocalCost.instructionWork code pc (.const rd value) ≤ 6 := by
  have span := (encodedLineWords_bound code pc).trans bounded
  have size := const_native_length_le rd value
  have encoding := riscvEnc_length_eq (.inst (.const rd value))
  change (riscvTarget.config.encode (.inst (.const rd value))).length =
    4 * (riscvAst (.inst (.const rd value))).length at encoding
  unfold LabToTarget.LocalCost.instructionWork
  simp only [instLocalCost]
  rw [encoding]
  omega

#print axioms native_instruction_encoding_min
#print axioms instructionWork_padding_five
#print axioms constantInstructionWork_six
end InitECandidate.Runtime.StackToLab
