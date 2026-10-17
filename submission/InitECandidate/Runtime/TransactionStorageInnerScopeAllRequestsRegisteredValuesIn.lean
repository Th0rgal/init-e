import InitECandidate.Runtime.TransactionStorageNewInnerAllRequestsRegisteredValuesIn
import InitECandidate.Runtime.TransactionStorageExistingInnerScopeRegisteredValuesIn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Both branches of the original inner-table scope terminate with a common
bound. The lookup-to-registry relation is explicit: every present inner pointer
must already be registered. No constructor-space premise is required. -/
theorem TransactionRegistryWorld.storage_inner_scope_all_requests_registered_values_in {F : Type}
    (state : PanSemStateFiniteExact 64 F) (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (fieldPointer ts journal snapshot count pointer outer addr key a b c d present inner : BitVec 64)
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (outerMember : outer ∈ tables) (innerMember : present ≠ 0 → inner ∈ tables)
    (outerLocal : state.locals.lookup (ofString "outer") = some (.val (.word outer)))
    (addrLocal : state.locals.lookup (ofString "addr") = some (.val (.word addr)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.rStruct [.val (.word a),.val (.word b),.val (.word c),.val (.word d)]))
    (mLocal : state.locals.lookup (ofString "m") = some (.rStruct [.val (.word present),.val (.word inner)]))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (addrAligned : addr.toNat % 8 = 0) (keyAligned : key.toNat % 8 = 0)
    (addrWords : ∀ offset : Nat, offset < (widths outer).toNat → state.memaddrs (addr + BitVec.ofNat 64 offset))
    (addrBytes : ∀ offset : Nat, offset < (widths outer).toNat → state.memaddrs (panByteAlignHOL (addr + BitVec.ofNat 64 offset)))
    (keyWords : ∀ offset : Nat, offset < (if present = 0 then (32 : BitVec 64) else widths inner).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (if present = 0 then (32 : BitVec 64) else widths inner).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (watched targets : Set (BitVec 64)) (watchedSubset : watched ⊆ tables)
    (registered : ∀ other ∈ watched, HashTableValuesIn other targets state)
    (saved : JournalSavedValuesIn journal count.toNat watched targets state)
    (newRegistered : present ≠ 0 → inner ∈ watched → pointer ∈ targets)
    (ticks : 2 ^ 76 + 19 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state stateStorageInnerScope = (result,post) ∧
      state.clock ≤ post.clock + (2 ^ 76 + 19) ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) →
        if present = 0 then
          TransactionRegistryWorld (withTableWidth widths pointer 32) (insert pointer tables) fieldPointer ts journal snapshot ((count + 1) + 1) post ∧
            (∀ other ∈ watched, HashTableValuesIn other (insert pointer targets) post) ∧
            JournalSavedValuesIn journal ((count + 1) + 1).toNat watched (insert pointer targets) post
        else TransactionRegistryWorld widths tables fieldPointer ts journal snapshot (count + 1) post ∧
            (∀ other ∈ watched, HashTableValuesIn other targets post) ∧
            JournalSavedValuesIn journal (count + 1).toNat watched targets post) := by
  by_cases missing : present = 0
  · subst present
    have keyNat : (32 : BitVec 64).toNat = 32 := rfl
    obtain ⟨result,post,run,cost,remaining,noTimeout,preserved⟩ := valid.storage_new_inner_scope_all_requests_registered_values_in state widths tables
      fieldPointer ts journal snapshot count pointer outer addr key a b c d inner outerMember outerLocal addrLocal keyLocal valueLocal mLocal heap
      addrAligned keyAligned addrWords addrBytes
      (by intro offset inside; apply keyWords offset; simpa [keyNat] using inside) (by intro offset inside; apply keyBytes offset; simpa [keyNat] using inside) watched targets watchedSubset registered saved ticks
    refine ⟨result,post,run,cost,remaining,noTimeout,?_⟩
    intro value success
    simpa using preserved value success
  · obtain ⟨result,post,run,cost,remaining,noTimeout,preserved⟩ := valid.storage_existing_inner_scope_registered_values_in state widths tables
      fieldPointer ts journal snapshot count pointer inner key a b c d present (innerMember missing) mLocal missing keyLocal valueLocal heap keyAligned
      (by simpa only [if_neg missing] using keyWords) (by simpa only [if_neg missing] using keyBytes) watched targets watchedSubset registered saved (newRegistered missing) (by omega)
    refine ⟨result,post,run,by omega,remaining,noTimeout,?_⟩
    intro value success
    simp only [if_neg missing]
    exact preserved value success

#print axioms TransactionRegistryWorld.storage_inner_scope_all_requests_registered_values_in
end InitECandidate.Runtime
