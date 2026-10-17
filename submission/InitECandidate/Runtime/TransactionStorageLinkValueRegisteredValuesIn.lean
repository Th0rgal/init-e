import InitECandidate.Runtime.TransactionStorageLinkValue
import InitECandidate.Runtime.TransactionStorageValueAllRequestsRegisteredValuesIn
import InitECandidate.Runtime.RegistryJournalSetRegisteredValuesIn
import InitECandidate.Runtime.TransactionRegistryHeapExists
import InitECandidate.Runtime.DiscardCallSuccessLocals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Linking an already registered new inner table into the outer map and
writing its value are jointly bounded, including allocation failure in jset or
the value tail. A successful return preserves two additional undo records. -/
theorem TransactionRegistryWorld.storage_link_and_value_registered_values_in {F : Type}
    (state : PanSemStateFiniteExact 64 F) (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (fieldPointer ts journal snapshot count outer inner addr key a b c d : BitVec 64)
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (outerMember : outer ∈ tables) (innerMember : inner ∈ tables)
    (outerLocal : state.locals.lookup (ofString "outer") = some (.val (.word outer)))
    (innerLocal : state.locals.lookup (ofString "inner") = some (.val (.word inner)))
    (addrLocal : state.locals.lookup (ofString "addr") = some (.val (.word addr)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.rStruct [.val (.word a),.val (.word b),.val (.word c),.val (.word d)]))
    (addrAligned : addr.toNat % 8 = 0) (keyAligned : key.toNat % 8 = 0)
    (addrWords : ∀ offset : Nat, offset < (widths outer).toNat → state.memaddrs (addr + BitVec.ofNat 64 offset))
    (addrBytes : ∀ offset : Nat, offset < (widths outer).toNat → state.memaddrs (panByteAlignHOL (addr + BitVec.ofNat 64 offset)))
    (keyWords : ∀ offset : Nat, offset < (widths inner).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (widths inner).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (watched targets : Set (BitVec 64)) (watchedSubset : watched ⊆ tables)
    (registered : ∀ other ∈ watched, HashTableValuesIn other targets state)
    (savedValues : JournalSavedValuesIn journal count.toNat watched targets state)
    (linkedRegistered : outer ∈ watched → inner ∈ targets)
    (innerUnwatched : inner ∉ watched)
    (ticks : 2 ^ 76 + 3 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state stateStorageLinkAndValue = (result,post) ∧
      state.clock ≤ post.clock + (2 ^ 76 + 3) ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) → TransactionRegistryWorld widths tables fieldPointer ts journal snapshot ((count + 1) + 1) post ∧
        (∀ other ∈ watched, HashTableValuesIn other targets post) ∧ JournalSavedValuesIn journal ((count + 1) + 1).toNat watched targets post) := by
  let call : ProgHOL 64 := .call (some (none,none)) (ofString "jset")
    [.var .local (ofString "outer"),.var .local (ofString "addr"),.var .local (ofString "inner")]
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.var .local (ofString "outer"),.var .local (ofString "addr"),.var .local (ofString "inner")] =
      some [.val (.word outer),.val (.word addr),.val (.word inner)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,outerLocal,addrLocal,innerLocal]
  have contract := valid.jset_call state widths tables fieldPointer ts journal snapshot count outer addr inner outerMember
    (.var .local (ofString "outer")) (.var .local (ofString "addr")) (.var .local (ofString "inner")) args addrAligned addrWords addrBytes (by omega)
  have jointContract := valid.jset_call_registered_values_in state widths tables fieldPointer ts journal snapshot count outer addr inner outerMember
    (.var .local (ofString "outer")) (.var .local (ofString "addr")) (.var .local (ofString "inner")) args addrAligned addrWords addrBytes (by omega)
    watched targets watchedSubset registered savedValues linkedRegistered
  cases callRun : evaluateHOLFiniteState state call with
  | mk result middle =>
    change (evaluateHOLFiniteState state call).1 ≠ some .timeOut ∧ state.clock ≤ (evaluateHOLFiniteState state call).2.clock + (2 ^ 73 + 1) ∧
      (evaluateHOLFiniteState state call).2.clock ≤ state.clock ∧ ((evaluateHOLFiniteState state call).1 = none →
        TransactionRegistryWorld widths tables fieldPointer ts journal snapshot (count + 1) (evaluateHOLFiniteState state call).2) at contract
    change (evaluateHOLFiniteState state call).1 ≠ some .timeOut ∧ _ at jointContract
    rw [callRun] at jointContract
    rw [callRun] at contract
    dsimp only at contract
    cases result with
    | none =>
      have midValid := contract.2.2.2 rfl
      have locals := evaluate_discard_call_success_locals state (ofString "jset")
        [.var .local (ofString "outer"),.var .local (ofString "addr"),.var .local (ofString "inner")] (by rw [show evaluateHOLFiniteState state _ = (none,middle) from callRun])
      change (evaluateHOLFiniteState state call).2.locals = state.locals at locals
      rw [callRun] at locals
      have metadata := evaluateHOLFiniteState_metadata state call
      rw [callRun] at metadata
      have domain : middle.memaddrs = state.memaddrs := metadata.2.1
      obtain ⟨pointer,heap,_,_,_⟩ := midValid.heap_exists
      obtain ⟨result,post,run,cost,remaining,noTimeout,preserved⟩ := midValid.storage_value_tail_all_requests_registered_values_in middle widths tables fieldPointer ts journal snapshot (count + 1) pointer inner key a b c d
        innerMember (by rw [locals]; exact innerLocal) (by rw [locals]; exact keyLocal) (by rw [locals]; exact valueLocal)
        heap keyAligned (by simpa only [domain] using keyWords) (by simpa only [domain] using keyBytes) watched targets watchedSubset (jointContract.2.2.2 rfl).2.1 (jointContract.2.2.2 rfl).2.2
        (fun belongs => False.elim (innerUnwatched belongs)) (by omega)
      refine ⟨result,post,?_,by omega,by omega,noTimeout,preserved⟩
      exact evaluate_seq_none callRun run
    | some result =>
      have run : evaluateHOLFiniteState state stateStorageLinkAndValue = (some result,middle) := by
        unfold stateStorageLinkAndValue
        rw [evaluateHOLFiniteState_seq_line780,callRun]
      refine ⟨some result,middle,run,?_,contract.2.2.1,contract.1,?_⟩
      · omega
      · intro value success
        have noReturn := evaluate_discard_call_no_return state (ofString "jset")
          [.var .local (ofString "outer"),.var .local (ofString "addr"),.var .local (ofString "inner")] value
        rw [show evaluateHOLFiniteState state _ = (some result,middle) from callRun] at noReturn
        exact False.elim (noReturn success)

#print axioms TransactionRegistryWorld.storage_link_and_value_registered_values_in
end InitECandidate.Runtime
