import InitECandidate.Runtime.GuestSpillPrices
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 10000000

private theorem riscv_stack_immediates : ∀ n : Fin 256,
    asmOffsetOkExact 0 riscvConfig.addrOffset (StackRemove.wordOffset n.val) = true := by
  decide_cbv

/-- Argument shuffles can span both small frames and still fit the signed
RISC-V memory immediate. The last legal nonnegative word offset is 255. -/
theorem riscv_stack_immediate (count : Nat) (small : count ≤ 255) :
    asmOffsetOkExact 0 riscvConfig.addrOffset (StackRemove.wordOffset count) = true :=
  riscv_stack_immediates ⟨count, by omega⟩

theorem riscv_stack_load_price (register count : Nat) (small : count ≤ 255) :
    removalLocalPrice 6 riscvConfig.addrOffset (.stackLoad register count) = 7 := by
  simp only [removalLocalPrice, riscv_stack_immediate count small, ↓reduceIte]

theorem riscv_stack_store_price (register count : Nat) (small : count ≤ 255) :
    removalLocalPrice 6 riscvConfig.addrOffset (.stackStore register count) = 7 := by
  simp only [removalLocalPrice, riscv_stack_immediate count small, ↓reduceIte]

#print axioms riscv_stack_immediate
#print axioms riscv_stack_load_price
#print axioms riscv_stack_store_price
end InitECandidate.Runtime.StackToLab
