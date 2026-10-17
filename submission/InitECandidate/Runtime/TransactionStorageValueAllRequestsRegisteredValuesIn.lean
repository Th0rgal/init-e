import InitECandidate.Runtime.TransactionStorageValueTailRegisteredValuesIn
import InitECandidate.Runtime.TransactionRegistryHeapBound
import InitECandidate.Runtime.AllocationFailureDeclarationNoTimeout
import InitECandidate.Runtime.AllocationFailureDeclarationNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every allocation request in the original storage value tail is bounded:
success retains the registry, while insufficient space terminates without return. -/
theorem TransactionRegistryWorld.storage_value_tail_all_requests_registered_values_in {F : Type}
    (state : PanSemStateFiniteExact 64 F) (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (fieldPointer ts journal snapshot count pointer inner key a b c d : BitVec 64)
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (member : inner ∈ tables)
    (innerLocal : state.locals.lookup (ofString "inner") = some (.val (.word inner)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.rStruct [.val (.word a),.val (.word b),.val (.word c),.val (.word d)]))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (widths inner).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (widths inner).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (watched targets : Set (BitVec 64)) (watchedSubset : watched ⊆ tables)
    (registered : ∀ other ∈ watched, HashTableValuesIn other targets state)
    (savedValues : JournalSavedValuesIn journal count.toNat watched targets state)
    (newRegistered : inner ∈ watched → pointer ∈ targets)
    (ticks : 2 ^ 75 + 2 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state stateStorageValueTail = (result,post) ∧
      state.clock ≤ post.clock + (2 ^ 75 + 2) ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) → TransactionRegistryWorld widths tables fieldPointer ts journal snapshot (count + 1) post ∧
        (∀ other ∈ watched, HashTableValuesIn other targets post) ∧ JournalSavedValuesIn journal (count + 1).toNat watched targets post) := by
  by_cases space : pointer.toNat + 32 ≤ 33806089496
  · exact valid.storage_value_tail_registered_values_in state widths tables fieldPointer ts journal snapshot count pointer inner key a b c d member
      innerLocal keyLocal valueLocal heap space keyAligned keyWords keyBytes watched targets watchedSubset registered savedValues newRegistered ticks
  · have pointerBound := valid.heap_bounded pointer heap
    have pointerLe : pointer ≤ (33806089496 : BitVec 64) := BitVec.le_def.mpr pointerBound
    have gap : ((33806089496 : BitVec 64) - pointer).toNat = 33806089496 - pointer.toNat := by
      rw [BitVec.toNat_sub_of_le pointerLe]; rfl
    have rejected : ((33806089496 : BitVec 64) - pointer).toNat < (32 : BitVec 64).toNat := by
      rw [gap]
      change _ < 32
      omega
    let continuation : ProgHOL 64 := .seq (.store (.var .local (ofString "v")) (.var .local (ofString "value")))
      (.seq (.call (some (none,none)) (ofString "jset")
        [.var .local (ofString "inner"),.var .local (ofString "key"),.var .local (ofString "v")]) (.return (.const 0)))
    have failure := evaluate_alloc_request_failure_declaration state (.const 32) pointer 32 (ofString "v") .one continuation rfl valid.journalWorld.code heap rejected
    have noTimeout := evaluate_alloc_request_failure_declaration_no_timeout state (.const 32) pointer 32 (ofString "v") .one continuation rfl valid.journalWorld.code heap rejected (by omega)
    have clock : (evaluateHOLFiniteState state stateStorageValueTail).2.clock = state.clock - 2 := failure.2
    refine ⟨_,_,rfl,?_,?_,noTimeout,?_⟩
    · change state.clock ≤ (evaluateHOLFiniteState state stateStorageValueTail).2.clock + (2 ^ 75 + 2)
      rw [clock]; omega
    · change (evaluateHOLFiniteState state stateStorageValueTail).2.clock ≤ state.clock
      rw [clock]; omega
    · intro value success
      have noReturn := evaluate_alloc_request_failure_declaration_no_return state (.const 32) pointer 32 (ofString "v") .one continuation value rfl valid.journalWorld.code heap rejected
      exact False.elim (noReturn success)

#print axioms TransactionRegistryWorld.storage_value_tail_all_requests_registered_values_in
end InitECandidate.Runtime
