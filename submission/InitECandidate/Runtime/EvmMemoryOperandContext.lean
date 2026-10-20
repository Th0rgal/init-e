import InitECandidate.Runtime.InterpreterFundingLayout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- Dynamic concrete words read by the memory/operand EVM instructions. -/
structure EvmMemoryOperandWords where
 pc : BitVec 64
 stackBase : BitVec 64
 stackSize : BitVec 64
 stackCapacity : BitVec 64
 memoryBase : BitVec 64
 memoryLength : BitVec 64
 memoryCapacity : BitVec 64
 framePointer : BitVec 64
 scratchPointer : BitVec 64
/-- Concrete physical state for the next real opcode. Operand storage lies
above scratch; extensible EVM memory ends below frame_mem_ptr and scratch. -/
structure EvmMemoryOperandAt {F : Type} (s : PanSemStateFiniteExact 64 F)
 (frame : BitVec 64) (words : EvmMemoryOperandWords) : Prop where
 ev : s.globals.lookup (ofString "ev")=some (.val (.word frame))
 framePointer : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word words.framePointer))
 scratchPointer : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word words.scratchPointer))
 headerDomain : ∀offset∈([0,8,16,24,32,40,232] : List (BitVec 64)),s.memaddrs (frame+offset)
 pc : s.memory (frame+0)=.word words.pc
 stackBase : s.memory (frame+8)=.word words.stackBase
 stackSize : s.memory (frame+16)=.word words.stackSize
 stackCapacity : s.memory (frame+232)=.word words.stackCapacity
 memoryBase : s.memory (frame+24)=.word words.memoryBase
 memoryLength : s.memory (frame+32)=.word words.memoryLength
 memoryCapacity : s.memory (frame+40)=.word words.memoryCapacity
 stackCapacityPositive : 1≤words.stackCapacity.toNat
 stackCapacityBound : words.stackCapacity.toNat≤1024
 stackSizeBound : words.stackSize.toNat≤words.stackCapacity.toNat
 stackLower : words.scratchPointer.toNat≤words.stackBase.toNat
 stackExtent : words.stackBase.toNat+32*words.stackCapacity.toNat≤frame.toNat
 memoryAligned : words.memoryLength.toNat%32=0
 memoryLengthBound : words.memoryLength.toNat≤words.memoryCapacity.toNat
 memoryExtent : words.memoryBase.toNat+words.memoryCapacity.toNat≤words.framePointer.toNat
 pointers : words.framePointer.toNat≤words.scratchPointer.toNat
 frameExtent : frame.toNat+280≤33806089496

theorem EvmMemoryOperandAt.scratch_before_frame {F : Type}
 {s : PanSemStateFiniteExact 64 F} {frame : BitVec 64} {words : EvmMemoryOperandWords}
 (valid : EvmMemoryOperandAt s frame words) : words.scratchPointer.toNat≤frame.toNat := by
 have first:=valid.stackLower;have second:=valid.stackExtent;omega
/-- The state predicate depends only on its actual globals, memory and domain. -/
theorem EvmMemoryOperandAt.after_context {F : Type}
 {s post : PanSemStateFiniteExact 64 F} {frame : BitVec 64} {words : EvmMemoryOperandWords}
 (valid : EvmMemoryOperandAt s frame words)
 (globals : post.globals=s.globals) (memory : post.memory=s.memory)
 (domain : post.memaddrs=s.memaddrs) : EvmMemoryOperandAt post frame words := by
 constructor
 · rw [globals];exact valid.ev
 · rw [globals];exact valid.framePointer
 · rw [globals];exact valid.scratchPointer
 · intro offset member;rw [domain];exact valid.headerDomain offset member
 · rw [memory];exact valid.pc
 · rw [memory];exact valid.stackBase
 · rw [memory];exact valid.stackSize
 · rw [memory];exact valid.stackCapacity
 · rw [memory];exact valid.memoryBase
 · rw [memory];exact valid.memoryLength
 · rw [memory];exact valid.memoryCapacity
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
#print axioms EvmMemoryOperandAt.scratch_before_frame
#print axioms EvmMemoryOperandAt.after_context
end InitECandidate.Runtime
