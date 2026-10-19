import InitECandidate.Runtime.StatelessBodyReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The nonempty transaction array is beyond the actual payload header. The empty
array needs no address separation. This uses the decoder's execution-linked cells. -/
theorem StatelessReturned.array_origin {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (input length offsets heap payload array count : BitVec 64)
    (decoded : StatelessReturned state input length offsets heap (.val (.word heap)) post)
    (payloadCell : post.memory (heap + 0) = .word payload)
    (arrayCell : post.memory (payload + 32) = .word array)
    (countCell : post.memory (payload + 40) = .word count) :
    count = 0 ∨ payload.toNat + 136 ≤ array.toNat := by
  obtain ⟨_,_,_,actualPayload,np,opl,ovh,orq,actualArray,actualCount,nextHeap,
    _,_,_,actualPayloadCell,_,_,actualArrayCell,actualCountCell,
    blobCell,blobCountCell,parentCell,long,mod,countBound,startBound,endBound,offsetOrder,
    inputAdd,inputSub,slices,wholeSlices,payloadExtent,arrayExtent,origin,frame⟩ := decoded
  have ep : actualPayload = payload := by simpa using actualPayloadCell.symm.trans payloadCell
  subst actualPayload
  have ea : actualArray = array := by simpa using actualArrayCell.symm.trans arrayCell
  subst actualArray
  have ec : actualCount = count := by simpa using actualCountCell.symm.trans countCell
  subst actualCount
  exact origin

#print axioms StatelessReturned.array_origin
end InitECandidate.Runtime
