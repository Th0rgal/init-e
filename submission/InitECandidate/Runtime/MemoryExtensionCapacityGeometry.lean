import InitECandidate.Runtime.MemoryExtensionSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def memoryExtensionCapacity (capacity newLength : BitVec 64) : BitVec 64 :=
 if (capacity*2#64).toNat<newLength.toNat then newLength+1024#64 else capacity*2#64

/-- The actual helper-derived expansion ceiling excludes both source addition
wraps before any successful workspace allocation is used. -/
theorem memory_extension_length_nonwrap (length capacity expansion : BitVec 64)
 (lengthBound : length.toNat≤capacity.toNat) (capacityBound : capacity.toNat≤33806089496)
 (expansionBound : expansion.toNat<2^38) :
 (length+expansion).toNat=length.toNat+expansion.toNat ∧
 (length+expansion+1024#64).toNat=length.toNat+expansion.toNat+1024 ∧
 (capacity*2#64).toNat=capacity.toNat*2 := by
 have sum : length.toNat+expansion.toNat<2^64:=by omega
 have added:=BitVec.toNat_add_of_lt sum
 refine ⟨added,?_,?_⟩
 · rw [BitVec.toNat_add_of_lt (by rw [added];change length.toNat+expansion.toNat+1024<2^64;omega),added];rfl
 · exact BitVec.toNat_mul_of_lt (by change capacity.toNat*2<2^64;omega)

theorem memory_extension_capacity_bounds (capacity newLength : BitVec 64)
 (capacityBound : capacity.toNat≤33806089496)
 (lengthBound : newLength.toNat≤33806089496+2^38)
 (growing : capacity.toNat<newLength.toNat) :
 capacity.toNat≤(memoryExtensionCapacity capacity newLength).toNat ∧
 newLength.toNat≤(memoryExtensionCapacity capacity newLength).toNat ∧
 (memoryExtensionCapacity capacity newLength).toNat<2^40 := by
 have doubled : (capacity*2#64).toNat=capacity.toNat*2 := BitVec.toNat_mul_of_lt (by change capacity.toNat*2<2^64;omega)
 have padded : (newLength+1024#64).toNat=newLength.toNat+1024 := BitVec.toNat_add_of_lt (by change newLength.toNat+1024<2^64;omega)
 unfold memoryExtensionCapacity
 split
 · rw [padded];omega
 · rw [doubled];omega

/-- Real allocator coverage then places the whole newly enlarged buffer below
scratch; the allocation premise is exactly what the source allocator returns. -/
theorem memory_extension_buffer_extent (base oldCapacity newCapacity pointer nextPointer scratch : BitVec 64)
 (oldExtent : base.toNat+oldCapacity.toNat≤pointer.toNat)
 (capacityOrder : oldCapacity.toNat≤newCapacity.toNat)
 (allocationCoverage : pointer.toNat+(newCapacity-oldCapacity).toNat≤nextPointer.toNat)
 (within : nextPointer.toNat≤scratch.toNat) :
 base.toNat+newCapacity.toNat≤nextPointer.toNat ∧base.toNat+newCapacity.toNat≤scratch.toNat := by
 rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr capacityOrder)] at allocationCoverage
 omega
#print axioms memory_extension_length_nonwrap
#print axioms memory_extension_capacity_bounds
#print axioms memory_extension_buffer_extent
end InitECandidate.Runtime
