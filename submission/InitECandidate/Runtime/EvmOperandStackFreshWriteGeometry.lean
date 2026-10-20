import InitECandidate.Runtime.EvmOperandStackWriteSuffix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The real four-word write for a fresh grown stack is strictly below the old
scratch frontier. No readability or room assumption is used for this geometry. -/
theorem stack_push_fresh_destination_below (base index capacity scratch offset : BitVec 64)
 (inside : index.toNat+1≤capacity.toNat) (capacityBound : capacity.toNat≤1024)
 (extent : base.toNat+capacity.toNat*32≤scratch.toNat)
 (scratchCap : scratch.toNat≤33806089496) (offsetBound : offset.toNat≤24) :
 (base+index*32#64+offset).toNat<scratch.toNat := by
 have product : (index*32#64).toNat=index.toNat*32 := by
  rw [BitVec.toNat_mul_of_lt (by change index.toNat*32<2^64;omega)];rfl
 have first : base.toNat+(index*32#64).toNat<2^64 := by rw [product];omega
 have second : (base+index*32#64).toNat+offset.toNat<2^64 := by
  rw [BitVec.toNat_add_of_lt first,product];omega
 rw [BitVec.toNat_add_of_lt second,BitVec.toNat_add_of_lt first,product]
 omega

theorem stack_push_fresh_destinations_domain {F : Type} (s : PanSemStateFiniteExact 64 F)
 (base index capacity scratch : BitVec 64)
 (inside : index.toNat+1≤capacity.toNat) (capacityBound : capacity.toNat≤1024)
 (extent : base.toNat+capacity.toNat*32≤scratch.toNat)
 (scratchCap : scratch.toNat≤33806089496)
 (fullDomain : ∀address : BitVec 64,address.toNat<33806089496 → s.memaddrs address) :
 ∀offset∈([0,8,16,24] : List (BitVec 64)),s.memaddrs (base+index*32+offset) := by
 intro offset member
 have offsetBound : offset.toNat≤24 := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl <;> decide
 have below:=stack_push_fresh_destination_below base index capacity scratch offset inside capacityBound extent scratchCap offsetBound
 apply fullDomain
 change (base+index*32#64+offset).toNat<33806089496
 omega

theorem stack_push_fresh_destinations_separate (base index capacity scratch watched : BitVec 64)
 (inside : index.toNat+1≤capacity.toNat) (capacityBound : capacity.toNat≤1024)
 (extent : base.toNat+capacity.toNat*32≤scratch.toNat)
 (scratchCap : scratch.toNat≤33806089496) (above : scratch.toNat≤watched.toNat) :
 ∀offset∈([0,8,16,24] : List (BitVec 64)),watched≠base+index*32+offset := by
 intro offset member equal
 have offsetBound : offset.toNat≤24 := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl <;> decide
 have below:=stack_push_fresh_destination_below base index capacity scratch offset inside capacityBound extent scratchCap offsetBound
 change watched=base+index*32#64+offset at equal
 have natural:=congrArg BitVec.toNat equal
 omega
#print axioms stack_push_fresh_destination_below
#print axioms stack_push_fresh_destinations_domain
#print axioms stack_push_fresh_destinations_separate
end InitECandidate.Runtime
