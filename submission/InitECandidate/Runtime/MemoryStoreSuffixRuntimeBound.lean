import InitECandidate.Runtime.MemoryStorePhysicalSource
import InitECandidate.Runtime.VmFn_sat_word
import InitECandidate.Runtime.VmFn_pc_add
import InitECandidate.Runtime.VmFn_u256_to_be32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
/-- Both original store suffixes are uniformly finite in every outcome. -/
theorem memory_store_suffix_bounded (kind : MemoryStorePhysicalKind) :
 ProgBounded (memoryStorePhysicalAt kind 3) 23 := by
 cases kind with
 | byte=>
  change ProgBounded (mstore8At 3) 23
  unfold mstore8At
  apply ProgBounded.weaken
  · vm_bound [vmBound_sat_word,vmBound_pc_add]
  · decide
 | word=>
  change ProgBounded (mstoreAt 3) 23
  unfold mstoreAt
  apply ProgBounded.weaken
  · vm_bound [vmBound_sat_word,vmBound_pc_add,vmBound_u256_to_be32]
  · decide
#print axioms memory_store_suffix_bounded
end InitECandidate.Runtime
