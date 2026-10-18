import InitECandidate.Runtime.SszSplitVarListSlicesBody
import InitECandidate.Runtime.AllocationAligned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A nonempty returned list has an exact, nonwrapping array allocation.
This combines the body heap/count contract with the LE32 slice contract;
no reserve for a successful allocation is assumed. -/
theorem sszSplitVarList_nonempty_returned_geometry {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (pointer length limit heapPointer : BitVec 64)
    (value : ValueHOL 64) (nonempty : length ≠ 0)
    (heapBound : heapPointer.toNat ≤ 33806089496) (aligned : heapPointer.toNat % 8 = 0)
    (body : SszSplitVarListReturned state length limit heapPointer value post)
    (slices : SszSplitVarListSlicesReturned state pointer length heapPointer post) :
    ∃ first : BitVec 64,
      first.toNat < 2 ^ 32 ∧ SszSplitFirstOK length first ∧
      value = .rStruct [.val (.word heapPointer),.val (.word (first >>> (2 : Nat)))] ∧
      ¬ limit < first >>> (2 : Nat) ∧ (first >>> (2 : Nat)).toNat < 2 ^ 30 ∧
      ((first >>> (2 : Nat)) * 16).toNat = (first >>> (2 : Nat)).toNat * 16 ∧
      heapPointer.toNat + (first >>> (2 : Nat)).toNat * 16 ≤ 33806089496 ∧
      (allocationEnd heapPointer ((first >>> (2 : Nat)) * 16)).toNat =
        heapPointer.toNat + (first >>> (2 : Nat)).toNat * 16 ∧
      post.globals = (setGlobalHOLFinite (ofString "heap_ptr")
        (.val (.word (allocationEnd heapPointer ((first >>> (2 : Nat)) * 16)))) state).globals ∧
      SszSplitSlices state.memory state.memaddrs pointer length first heapPointer (first >>> (2 : Nat)) post.memory := by
  rcases body with ⟨zero,_,_⟩ | ⟨_,first,read,ok,returned,within,request,globals⟩
  · exact False.elim (nonempty zero)
  · rcases slices with ⟨zero,_⟩ | ⟨sliceFirst,sliceRead,small,cells⟩
    · exact False.elim (nonempty zero)
    · have same : sliceFirst = first := by
        have equal := Option.some.inj (sliceRead.symm.trans read)
        simpa using equal
      subst sliceFirst
      have countNat : (first >>> (2 : Nat)).toNat = first.toNat / 4 := by
        rw [BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
      have countSmall : (first >>> (2 : Nat)).toNat < 2 ^ 30 := by omega
      have product : ((first >>> (2 : Nat)) * 16).toNat = (first >>> (2 : Nat)).toNat * 16 := by
        apply BitVec.toNat_mul_of_lt
        change (first >>> (2 : Nat)).toNat * 16 < 2 ^ 64
        omega
      have available : ((33806089496 : BitVec 64) - heapPointer).toNat = 33806089496 - heapPointer.toNat := by
        rw [BitVec.toNat_sub_of_le (show heapPointer ≤ (33806089496 : BitVec 64) from heapBound)]
        rfl
      have capacity : heapPointer.toNat + (first >>> (2 : Nat)).toNat * 16 ≤ 33806089496 := by
        change ((first >>> (2 : Nat)) * 16).toNat ≤ ((33806089496 : BitVec 64) - heapPointer).toNat at request
        rw [product,available] at request
        omega
      have endNat := allocationEnd_aligned_toNat heapPointer ((first >>> (2 : Nat)) * 16)
        (by rw [product]; exact capacity) aligned (by rw [product]; omega)
      rw [product] at endNat
      exact ⟨first,small,ok,returned,within,countSmall,product,capacity,endNat,globals,cells⟩

#print axioms sszSplitVarList_nonempty_returned_geometry
end InitECandidate.Runtime
