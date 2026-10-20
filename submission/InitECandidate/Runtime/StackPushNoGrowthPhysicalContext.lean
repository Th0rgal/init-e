import InitECandidate.Runtime.EvmMemoryOperandContext
import InitECandidate.Runtime.EvmOperandStackNoGrowth
import InitECandidate.Runtime.EvmOperandStackFreshWriteGeometry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Whole real stack_push when its actual input index is below capacity. The
owned operand write and actual counter increment close the next physical state. -/
theorem stack_push_no_growth_returned_physical_context {F : Type}
 (s post : PanSemStateFiniteExact 64 F) (frame : BitVec 64)
 (words : EvmMemoryOperandWords) (valid : EvmMemoryOperandAt s frame words)
 (a b c d : BitVec 64) (value : ValueHOL 64)
 (atValue : s.locals.lookup (ofString "v")=some (fundingU256 a b c d))
 (inside : words.stackSize.toNat<words.stackCapacity.toNat)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496→s.memaddrs address)
 (run : evaluateHOLFiniteState s (stackPushAt 0)=(some (.returned value),post)) :
 value=.val (.word 0) ∧
 EvmMemoryOperandAt post frame {words with stackSize:=words.stackSize+1} ∧
 post.globals=s.globals ∧post.memaddrs=s.memaddrs ∧post.be=s.be ∧post.code=s.code ∧
 (∀watched : BitVec 64,frame.toNat≤watched.toNat→watched≠frame+16→post.memory watched=s.memory watched) := by
 have extent : words.stackBase.toNat+words.stackCapacity.toNat*32≤frame.toNat := by simpa only [Nat.mul_comm] using valid.stackExtent
 have frameCap : frame.toNat≤33806089496 := by have bound:=valid.frameExtent;omega
 have destinations:=stack_push_fresh_destinations_domain s words.stackBase words.stackSize words.stackCapacity frame (by omega) valid.stackCapacityBound extent frameCap fullDomain
 have domains : ∀offset∈([8,16,232] : List (BitVec 64)),s.memaddrs (frame+offset) := by
  intro offset member;exact valid.headerDomain offset (by simp only [List.mem_cons,List.not_mem_nil,or_false] at member ⊢;tauto)
 obtain ⟨zero,memory,globals,clock,domain,endian,installed⟩:=stack_push_no_growth_returned s post frame words.stackBase words.stackSize words.stackCapacity a b c d value valid.ev atValue domains valid.stackBase valid.stackSize valid.stackCapacity inside valid.stackCapacityBound destinations run
 have upperFrame (watched : BitVec 64) (above : frame.toNat≤watched.toNat) (different : watched≠frame+16) : post.memory watched=s.memory watched := by
  rw [memory]
  exact stack_push_write_suffix_frame s frame words.stackBase words.stackSize a b c d watched different (stack_push_fresh_destinations_separate words.stackBase words.stackSize words.stackCapacity frame watched (by omega) valid.stackCapacityBound extent frameCap above)
 have headerKept (offset : BitVec 64) (small : offset.toNat<280) (different : offset≠16#64) : post.memory (frame+offset)=s.memory (frame+offset) := by
  have natural : (frame+offset).toNat=frame.toNat+offset.toNat:=BitVec.toNat_add_of_lt (by have bound:=valid.frameExtent;omega)
  apply upperFrame _ (by rw [natural];omega)
  intro same;exact different (add_left_cancel same)
 have indexNatural : (words.stackSize+1#64).toNat=words.stackSize.toNat+1 := by
  rw [BitVec.toNat_add_of_lt (by change words.stackSize.toNat+1<2^64;have bound:=valid.stackCapacityBound;omega)]
  rfl
 refine ⟨zero,?_,globals,domain,endian,installed,upperFrame⟩
 constructor
 · rw [globals];exact valid.ev
 · rw [globals];exact valid.framePointer
 · rw [globals];exact valid.scratchPointer
 · intro offset member;rw [domain];exact valid.headerDomain offset member
 · exact (headerKept 0 (by decide) (by decide)).trans valid.pc
 · exact (headerKept 8 (by decide) (by decide)).trans valid.stackBase
 · rw [memory];simp [stackPushWritePost,sourceWriteWord]
 · exact (headerKept 232 (by decide) (by decide)).trans valid.stackCapacity
 · exact (headerKept 24 (by decide) (by decide)).trans valid.memoryBase
 · exact (headerKept 32 (by decide) (by decide)).trans valid.memoryLength
 · exact (headerKept 40 (by decide) (by decide)).trans valid.memoryCapacity
 · exact valid.stackCapacityPositive
 · exact valid.stackCapacityBound
 · change (words.stackSize+1#64).toNat≤words.stackCapacity.toNat
   rw [indexNatural];omega
 · exact valid.stackLower
 · exact valid.stackExtent
 · exact valid.memoryAligned
 · exact valid.memoryLengthBound
 · exact valid.memoryExtent
 · exact valid.pointers
 · exact valid.frameExtent
#print axioms stack_push_no_growth_returned_physical_context
end InitECandidate.Runtime
