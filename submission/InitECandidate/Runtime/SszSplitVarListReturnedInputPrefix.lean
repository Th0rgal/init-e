import InitECandidate.Runtime.SszSplitVarListReturnedGeometry
import InitECandidate.Runtime.SszSplitSlicesInputPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Empty and nonempty returned lists both supply readable bounded input
slices and an aligned, capped heap beyond the complete array allocation. -/
theorem sszSplitVarList_returned_input_prefix {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (pointer length limit heapPointer : BitVec 64)
    (value : ValueHOL 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (aligned : heapPointer.toNat % 8 = 0)
    (domain : post.memaddrs = state.memaddrs) (inputFits : pointer.toNat + length.toNat < 2 ^ 64)
    (body : SszSplitVarListReturned state length limit heapPointer value post)
    (slices : SszSplitVarListSlicesReturned state pointer length heapPointer post) :
    ∃ array count nextHeap : BitVec 64,
      value = .rStruct [.val (.word array),.val (.word count)] ∧
      RlpSliceInputPrefix post array pointer length count.toNat ∧ count.toNat ≤ length.toNat / 4 ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat % 8 = 0 ∧
      heapPointer.toNat ≤ nextHeap.toNat ∧ array.toNat + count.toNat * 16 ≤ nextHeap.toNat := by
  by_cases zero : length = 0
  · rcases body with ⟨_,returned,globals⟩ | ⟨notShort,_⟩
    · refine ⟨0,0,heapPointer,returned,?_,?_,?_,heapBound,aligned,by omega,?_⟩
      · exact rlpSliceInputPrefix_empty post 0 pointer length
      · simp
      · rw [globals]; exact heap
      · simp
    · exact False.elim (notShort (by simp [zero]))
  · obtain ⟨first,small,ok,returned,within,countSmall,product,capacity,endNat,globals,cells⟩ :=
      sszSplitVarList_nonempty_returned_geometry state post pointer length limit heapPointer value zero heapBound aligned body slices
    have inputPrefix := sszSplitSlices_input_prefix state post pointer length first heapPointer (first >>> (2 : Nat))
      domain inputFits cells
    have countNat : (first >>> (2 : Nat)).toNat = first.toNat / 4 := by
      rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
    have firstLe : first.toNat ≤ length.toNat := by
      have bound := ok.2.2
      change ¬ length.toNat < first.toNat at bound
      omega
    have countLe : (first >>> (2 : Nat)).toNat ≤ length.toNat / 4 := by
      rw [countNat]
      exact Nat.div_le_div_right firstLe
    let nextHeap := allocationEnd heapPointer ((first >>> (2 : Nat)) * 16)
    have nextNat : nextHeap.toNat = heapPointer.toNat + (first >>> (2 : Nat)).toNat * 16 := endNat
    refine ⟨heapPointer,first >>> (2 : Nat),nextHeap,returned,inputPrefix,countLe,?_,?_,?_,?_,?_⟩
    · rw [globals]
      simp [nextHeap,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · rw [nextNat]; exact capacity
    · rw [nextNat]
      omega
    · rw [nextNat]; omega
    · rw [nextNat]

#print axioms sszSplitVarList_returned_input_prefix
end InitECandidate.Runtime
