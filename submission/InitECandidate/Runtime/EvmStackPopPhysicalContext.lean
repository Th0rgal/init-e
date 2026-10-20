import InitECandidate.Runtime.EvmMemoryOperandContext
import InitECandidate.Runtime.EvmStackPopReturnedFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Whole real stack_pop preserves the concrete next-opcode physical state,
with its actual counter decremented; actual return excludes underflow. -/
theorem stack_pop_returned_physical_context {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (frame : BitVec 64)
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s frame words)
 (value : ValueHOL 64)
 (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_stack_pop)=(some (.returned value),post)) :
 0<words.stackSize.toNat ∧
 EvmMemoryOperandAt post frame {words with stackSize:=words.stackSize-1} ∧
 (∀watched : BitVec 64,watched≠frame+16→post.memory watched=s.memory watched) ∧
 post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code := by
 obtain ⟨positive,memory,globals,clock,domain,endian,installed⟩:=stack_pop_body_returned_frame s post frame words.stackSize value valid.ev (valid.headerDomain 16 (by simp)) valid.stackSize run
 have keep (watched : BitVec 64) (different : watched≠frame+16#64) : post.memory watched=s.memory watched := by
  rw [memory]
  change (if watched=frame+16#64 then _ else _)=_
  rw [if_neg different]
 have decrement : (words.stackSize-1#64).toNat=words.stackSize.toNat-1 := BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change (1#64).toNat≤words.stackSize.toNat;change 1≤words.stackSize.toNat;omega))
 refine ⟨positive,?_,keep,globals,domain,endian,installed⟩
 constructor
 · rw [globals];exact valid.ev
 · rw [globals];exact valid.framePointer
 · rw [globals];exact valid.scratchPointer
 · intro offset member;rw [domain];exact valid.headerDomain offset member
 · exact (keep (frame+0) (by intro equal;exact (by decide : (0#64)≠16#64) (add_left_cancel equal))).trans valid.pc
 · exact (keep (frame+8) (by intro equal;exact (by decide : (8#64)≠16#64) (add_left_cancel equal))).trans valid.stackBase
 · rw [memory];simp [sourceWriteWord]
 · exact (keep (frame+232) (by intro equal;exact (by decide : (232#64)≠16#64) (add_left_cancel equal))).trans valid.stackCapacity
 · exact (keep (frame+24) (by intro equal;exact (by decide : (24#64)≠16#64) (add_left_cancel equal))).trans valid.memoryBase
 · exact (keep (frame+32) (by intro equal;exact (by decide : (32#64)≠16#64) (add_left_cancel equal))).trans valid.memoryLength
 · exact (keep (frame+40) (by intro equal;exact (by decide : (40#64)≠16#64) (add_left_cancel equal))).trans valid.memoryCapacity
 · exact valid.stackCapacityPositive
 · exact valid.stackCapacityBound
 · change (words.stackSize-1#64).toNat≤words.stackCapacity.toNat
   rw [decrement];have bound:=valid.stackSizeBound;omega
 · exact valid.stackLower
 · exact valid.stackExtent
 · exact valid.memoryAligned
 · exact valid.memoryLengthBound
 · exact valid.memoryExtent
 · exact valid.pointers
 · exact valid.frameExtent
#print axioms stack_pop_returned_physical_context
end InitECandidate.Runtime
