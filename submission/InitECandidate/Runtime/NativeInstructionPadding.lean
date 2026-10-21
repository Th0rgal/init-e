import InitECandidate.Runtime.StackNativeLocalPrice
import InitECandidate.Runtime.InstBudget
import InitECandidate.Runtime.LabInstructionPaddingBounds
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.LabLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.LabToTarget Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Encoders.RiscV.Target Flapjack.RiscV.TargetProof

/-- The local span already contains the encoded instruction. Only the
remaining bytes are padding, so a six-word span permits at most five padding
instructions, not six extra ones. -/
theorem instructionWork_padding_five (code : LabProgHOL 64)
    (bounded : encodedLineWords code ≤ 6) (pc : Nat) (instruction : HolInst 64) :
    LabToTarget.LocalCost.instructionWork code pc instruction ≤ instLocalCost instruction + 5 := by
  exact instructionWork_padding_bound code pc 6 instruction
    ((encodedLineWords_bound code pc).trans bounded)

/-- Literal encoding and following padding share the same six-word span.
Their costs must not be added as two independent worst cases. -/
theorem constantInstructionWork_six (code : LabProgHOL 64)
    (bounded : encodedLineWords code ≤ 6) (pc rd : Nat) (value : BitVec 64) :
    LabToTarget.LocalCost.instructionWork code pc (.const rd value) ≤ 6 := by
  have bound := constantInstructionWork_max code pc 6 rd value
    ((encodedLineWords_bound code pc).trans bounded)
  have size := const_native_length_le rd value
  exact bound.trans (max_le size (Nat.le_refl _))

#print axioms native_instruction_encoding_min
#print axioms instructionWork_padding_five
#print axioms constantInstructionWork_six
end InitECandidate.Runtime.StackToLab
