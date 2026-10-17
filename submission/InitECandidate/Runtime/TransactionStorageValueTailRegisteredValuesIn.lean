import InitECandidate.Runtime.StateStorageValueTail
import InitECandidate.Runtime.TransactionStorageValueRegisteredValuesIn
import InitECandidate.Runtime.RegistryJournalSetRegisteredValuesIn
import InitECandidate.Runtime.PanEvaluationMetadata
import InitECandidate.Runtime.DiscardCallNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual storage value-allocation/update/return tail retains the full
registry on successful return and cannot time out within2^73+2 source clocks.
The selected inner table must already be registered by the preceding branch. -/
theorem TransactionRegistryWorld.storage_value_tail_registered_values_in {F : Type}
    (state : PanSemStateFiniteExact 64 F) (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (fieldPointer ts journal snapshot count pointer inner key a b c d : BitVec 64)
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (member : inner ∈ tables)
    (innerLocal : state.locals.lookup (ofString "inner") = some (.val (.word inner)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.rStruct [.val (.word a),.val (.word b),.val (.word c),.val (.word d)]))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (space : pointer.toNat + 32 ≤ 33806089496)
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
  obtain ⟨middle,prefixRun,midValid,midValues,midSaved,clock,atV,_,locals,_,_,_,_⟩ := valid.allocate_storage_value_registered_values_in state widths tables fieldPointer ts journal snapshot count pointer a b c d
    valueLocal heap watched targets watchedSubset registered savedValues space (by omega)
  have metadata := evaluateHOLFiniteState_metadata state
    (.decCall (ofString "v") .one (ofString "alloc") [.const 32]
      (.seq (.store (.var .local (ofString "v")) (.var .local (ofString "value"))) .skip))
  rw [prefixRun,evaluateHOLFiniteState_skip] at metadata
  have domain : middle.memaddrs = state.memaddrs := metadata.2.1
  have atInner : middle.locals.lookup (ofString "inner") = some (.val (.word inner)) := by
    rw [locals]
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "v" ≠ ofString "inner" from by decide] using innerLocal
  have atKey : middle.locals.lookup (ofString "key") = some (.val (.word key)) := by
    rw [locals]
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "v" ≠ ofString "key" from by decide] using keyLocal
  let call : ProgHOL 64 := .call (some (none,none)) (ofString "jset")
    [.var .local (ofString "inner"),.var .local (ofString "key"),.var .local (ofString "v")]
  have args : evalListHOLFinite middle (h := fun address => Classical.propDecidable (middle.memaddrs address))
      [.var .local (ofString "inner"),.var .local (ofString "key"),.var .local (ofString "v")] =
      some [.val (.word inner),.val (.word key),.val (.word pointer)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,atInner,atKey,atV]
  have contract := midValid.jset_call middle widths tables fieldPointer ts journal snapshot count inner key pointer member
    (.var .local (ofString "inner")) (.var .local (ofString "key")) (.var .local (ofString "v")) args keyAligned
    (by simpa only [domain] using keyWords) (by simpa only [domain] using keyBytes) (by omega)
  have jointContract := midValid.jset_call_registered_values_in middle widths tables fieldPointer ts journal snapshot count inner key pointer member
    (.var .local (ofString "inner")) (.var .local (ofString "key")) (.var .local (ofString "v")) args keyAligned
    (by simpa only [domain] using keyWords) (by simpa only [domain] using keyBytes) (by omega)
    watched targets watchedSubset midValues midSaved newRegistered
  have full : evaluateHOLFiniteState state stateStorageValueTail =
      (let output := evaluateHOLFiniteState middle (.seq call (.return (.const 0)));
        (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (ofString "v",state.locals.lookup (ofString "v"))})) :=
    prefixRun (.seq call (.return (.const 0)))
  cases callRun : evaluateHOLFiniteState middle call with
  | mk result afterCall =>
    change (evaluateHOLFiniteState middle call).1 ≠ some .timeOut ∧ middle.clock ≤ (evaluateHOLFiniteState middle call).2.clock + (2 ^ 73 + 1) ∧ (evaluateHOLFiniteState middle call).2.clock ≤ middle.clock ∧
      ((evaluateHOLFiniteState middle call).1 = none → TransactionRegistryWorld widths tables fieldPointer ts journal snapshot (count + 1) (evaluateHOLFiniteState middle call).2) at contract
    change (evaluateHOLFiniteState middle call).1 ≠ some .timeOut ∧ _ at jointContract
    rw [callRun] at jointContract
    rw [callRun] at contract
    change result ≠ some .timeOut ∧ middle.clock ≤ afterCall.clock + (2 ^ 73 + 1) ∧ afterCall.clock ≤ middle.clock ∧
      (result = none → TransactionRegistryWorld widths tables fieldPointer ts journal snapshot (count + 1) afterCall) at contract
    cases result with
    | none =>
      have returned : evaluateHOLFiniteState middle (.seq call (.return (.const 0))) =
          (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite afterCall) := by
        rw [evaluateHOLFiniteState_seq_line780,callRun]
        simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
      rw [returned] at full
      dsimp only at full
      refine ⟨_,_,full,?_,?_,by simp,?_⟩
      · change state.clock ≤ afterCall.clock + (2 ^ 75 + 2)
        omega
      · change afterCall.clock ≤ state.clock
        omega
      · intro value success
        have joint := jointContract.2.2.2 rfl
        exact ⟨joint.1.after_read rfl rfl rfl rfl rfl,
          (fun other belongs => (joint.2.1 other belongs).after_read rfl rfl rfl),
          joint.2.2.after_frame (Nat.le_refl _) (by intro index inside offset belongs; rfl)⟩
    | some result =>
      have terminal : evaluateHOLFiniteState middle (.seq call (.return (.const 0))) = (some result,afterCall) := by
        rw [evaluateHOLFiniteState_seq_line780,callRun]
      rw [terminal] at full
      dsimp only at full
      refine ⟨_,_,full,?_,?_,contract.1,?_⟩
      · change state.clock ≤ afterCall.clock + (2 ^ 75 + 2)
        omega
      · change afterCall.clock ≤ state.clock
        omega
      · intro value success
        have noReturn := evaluate_discard_call_no_return middle (ofString "jset")
          [.var .local (ofString "inner"),.var .local (ofString "key"),.var .local (ofString "v")] value
        rw [show evaluateHOLFiniteState middle (.call (some (none,none)) (ofString "jset")
          [.var .local (ofString "inner"),.var .local (ofString "key"),.var .local (ofString "v")]) = (some result,afterCall) from callRun] at noReturn
        exact False.elim (noReturn success)

#print axioms TransactionRegistryWorld.storage_value_tail_registered_values_in
end InitECandidate.Runtime
