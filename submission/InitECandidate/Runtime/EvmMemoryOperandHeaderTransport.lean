import InitECandidate.Runtime.EvmMemoryOperandContext
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
theorem EvmMemoryOperandAt.after_header_frame {F : Type}
 {s post : PanSemStateFiniteExact 64 F} {frame : BitVec 64} {words : EvmMemoryOperandWords}
 (valid : EvmMemoryOperandAt s frame words)
 (globals : post.globals=s.globals) (memory : ∀offset∈([0,8,16,24,32,40,232] : List (BitVec 64)),post.memory (frame+offset)=s.memory (frame+offset))
 (domain : post.memaddrs=s.memaddrs) : EvmMemoryOperandAt post frame words := by
 constructor
 · rw [globals];exact valid.ev
 · rw [globals];exact valid.framePointer
 · rw [globals];exact valid.scratchPointer
 · intro offset member;rw [domain];exact valid.headerDomain offset member
 · exact (memory 0 (by simp)).trans valid.pc
 · exact (memory 8 (by simp)).trans valid.stackBase
 · exact (memory 16 (by simp)).trans valid.stackSize
 · exact (memory 232 (by simp)).trans valid.stackCapacity
 · exact (memory 24 (by simp)).trans valid.memoryBase
 · exact (memory 32 (by simp)).trans valid.memoryLength
 · exact (memory 40 (by simp)).trans valid.memoryCapacity
 · exact valid.stackCapacityPositive
 · exact valid.stackCapacityBound
 · exact valid.stackSizeBound
 · exact valid.stackLower
 · exact valid.stackExtent
 · exact valid.memoryAligned
 · exact valid.memoryLengthBound
 · exact valid.memoryExtent
 · exact valid.pointers
 · exact valid.frameExtent
#print axioms EvmMemoryOperandAt.after_header_frame
end InitECandidate.Runtime
