import InitECandidate.Runtime.StackRemovalLocalPrice
import Flapjack.Compiler.Encoders.RiscV.Target
namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Encoders.RiscV.Target
set_option cbv.maxSteps 10000000
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

private theorem riscv_small_offsets : ∀ n : Fin 92,
    asmOffsetOkExact 0 riscvConfig.addrOffset (StackRemove.wordOffset n.val) = true := by
  decide_cbv

theorem riscv_spill_offset (count : Nat) (small : count ≤ 91) :
    asmOffsetOkExact 0 riscvConfig.addrOffset (StackRemove.wordOffset count) = true :=
  riscv_small_offsets ⟨count, by omega⟩

theorem guest_spill_load_price (reg count : Nat) (small : count ≤ 91) :
    removalLocalPrice 6 riscvConfig.addrOffset (.stackLoad reg count) = 7 := by
  simp only [removalLocalPrice, riscv_spill_offset count small, ↓reduceIte]

theorem guest_spill_store_price (reg count : Nat) (small : count ≤ 91) :
    removalLocalPrice 6 riscvConfig.addrOffset (.stackStore reg count) = 7 := by
  simp only [removalLocalPrice, riscv_spill_offset count small, ↓reduceIte]

theorem guest_frame_alloc_price (count : Nat) (small : count ≤ 92) :
    removalLocalPrice 6 riscvConfig.addrOffset (.stackAlloc count) ≤ 25 := by
  simp only [removalLocalPrice]
  have : (count + 254) / 255 ≤ 1 := by omega
  omega

theorem guest_frame_free_price (count : Nat) (small : count ≤ 92) :
    removalLocalPrice 6 riscvConfig.addrOffset (.stackFree count) ≤ 7 := by
  simp only [removalLocalPrice]
  have : (count + 254) / 255 ≤ 1 := by omega
  omega

#print axioms riscv_spill_offset
#print axioms guest_spill_load_price
#print axioms guest_spill_store_price
#print axioms guest_frame_alloc_price
#print axioms guest_frame_free_price
end InitECandidate.Runtime.StackToLab
