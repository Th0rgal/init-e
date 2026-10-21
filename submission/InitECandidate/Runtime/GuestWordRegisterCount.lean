import Flapjack.Compiler.Encoders.RiscV.Target.Configuration
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target

/-- The pinned RISC-V compiler leaves exactly 22 allocatable Word registers.
This discharges the quantitative simulation's register guard at compileNative. -/
theorem guest_word_register_count :
    riscvConfig.regCount - (5 + riscvConfig.avoidRegs.length) = 22 := by
  decide

#print axioms guest_word_register_count
end InitECandidate.Runtime.WordToStack
