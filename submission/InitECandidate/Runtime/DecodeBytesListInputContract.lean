import InitECandidate.Runtime.DecodeBytesListReturnedAligned
import InitECandidate.Runtime.SszSplitVarListReturnedInputPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual returned byte-list decoder supplies the bounded readable input
slices and array/heap extent needed by the node-database builder. Empty lists
are covered with their original zero array pointer. -/
theorem decodeBytesList_returned_input_prefix {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (pointer length limit maxBytes heapPointer : BitVec 64)
    (value : ValueHOL 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (aligned : heapPointer.toNat % 8 = 0)
    (inputFits : pointer.toNat + length.toNat < 2^64)
    (returned : DecodeBytesListReturned state pointer length limit maxBytes heapPointer value post) :
    ∃ array count nextHeap : BitVec 64,
      value = .rStruct [.val (.word array),.val (.word count)] ∧
      RlpSliceInputPrefix post array pointer length count.toNat ∧ count.toNat ≤ length.toNat / 4 ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat % 8 = 0 ∧
      heapPointer.toNat ≤ nextHeap.toNat ∧ array.toNat + count.toNat * 16 ≤ nextHeap.toNat := by
  obtain ⟨clock,bodyPost,run,body,slices,memory,globals,domain,items⟩ := returned
  let entry : PanSemStateFiniteExact 64 F :=
    {callEntryStateHOLFinite state (bytesListSplitLocals pointer length limit) with clock := clock}
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_ssz_split_var_list)
  rw [run] at metadata
  obtain ⟨array,count,nextHeap,shape,decoded,countLe,heapGlobal,capped,al,monotone,extent⟩ :=
    sszSplitVarList_returned_input_prefix entry bodyPost pointer length limit heapPointer value heap heapBound aligned
      metadata.2.1 inputFits body slices
  refine ⟨array,count,nextHeap,shape,?_,countLe,?_,capped,al,monotone,extent⟩
  · intro j inside
    obtain ⟨src,len,valid⟩ := decoded j inside
    exact ⟨src,len,valid.after_frame bodyPost post array j src len pointer length domain
      (congrFun memory _) (congrFun memory _)⟩
  · rw [globals]; exact heapGlobal

#print axioms decodeBytesList_returned_input_prefix
end InitECandidate.Runtime
