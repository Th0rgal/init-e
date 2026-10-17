import InitECandidate.Runtime.TransactionStorageNewInnerExactSpaceRegisteredValuesIn
import InitECandidate.Runtime.TransactionStorageInsufficientSpace
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original missing-inner branch has a bound for every heap frontier.
Successful returns retain the enlarged transaction registry; heap exhaustion
terminates through the constructor rejection path. No reserve is assumed. -/
theorem TransactionRegistryWorld.storage_new_inner_all_requests_registered_values_in {F : Type}
    (state : PanSemStateFiniteExact 64 F) (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (fieldPointer ts journal snapshot count pointer outer addr key a b c d oldInner lookupValue : BitVec 64)
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (outerMember : outer ∈ tables)
    (innerLocal : state.locals.lookup (ofString "inner") = some (.val (.word oldInner)))
    (outerLocal : state.locals.lookup (ofString "outer") = some (.val (.word outer)))
    (addrLocal : state.locals.lookup (ofString "addr") = some (.val (.word addr)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.rStruct [.val (.word a),.val (.word b),.val (.word c),.val (.word d)]))
    (mLocal : state.locals.lookup (ofString "m") = some (.rStruct [.val (.word (0 : BitVec 64)),.val (.word lookupValue)]))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (addrAligned : addr.toNat % 8 = 0) (keyAligned : key.toNat % 8 = 0)
    (addrWords : ∀ offset : Nat, offset < (widths outer).toNat → state.memaddrs (addr + BitVec.ofNat 64 offset))
    (addrBytes : ∀ offset : Nat, offset < (widths outer).toNat → state.memaddrs (panByteAlignHOL (addr + BitVec.ofNat 64 offset)))
    (keyWords : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (watched targets : Set (BitVec 64)) (watchedSubset : watched ⊆ tables)
    (registered : ∀ other ∈ watched, HashTableValuesIn other targets state)
    (saved : JournalSavedValuesIn journal count.toNat watched targets state)
    (ticks : 2 ^ 76 + 19 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state stateStorageInnerSelection = (result,post) ∧
      state.clock ≤ post.clock + (2 ^ 76 + 19) ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) → TransactionRegistryWorld (withTableWidth widths pointer 32)
        (insert pointer tables) fieldPointer ts journal snapshot ((count + 1) + 1) post ∧
        (∀ other ∈ watched, HashTableValuesIn other (insert pointer targets) post) ∧
        JournalSavedValuesIn journal ((count + 1) + 1).toNat watched (insert pointer targets) post) := by
  by_cases space : pointer.toNat + 528 ≤ 33806089496
  · exact valid.storage_new_inner_exact_space_registered_values_in state widths tables fieldPointer ts journal snapshot count pointer outer addr key a b c d oldInner lookupValue
      outerMember innerLocal outerLocal addrLocal keyLocal valueLocal mLocal heap space addrAligned keyAligned addrWords addrBytes keyWords keyBytes watched targets watchedSubset registered saved ticks
  · have failure := valid.storage_new_inner_insufficient_space state widths tables fieldPointer ts journal snapshot count pointer lookupValue
      mLocal heap space (by omega)
    let output := evaluateHOLFiniteState state stateStorageInnerSelection
    refine ⟨output.1,output.2,rfl,?_,failure.2.2.2.2,failure.2.1,?_⟩
    · have cost := failure.2.2.2.1
      change state.clock ≤ output.2.clock + 17 at cost
      omega
    · intro value success
      exact False.elim (failure.2.2.1 value success)

/-- The original inner declaration also has the complete no-reserve bound
and restores caller locals while retaining the successful registry invariant. -/
theorem TransactionRegistryWorld.storage_new_inner_scope_all_requests_registered_values_in {F : Type}
    (state : PanSemStateFiniteExact 64 F) (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (fieldPointer ts journal snapshot count pointer outer addr key a b c d lookupValue : BitVec 64)
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (outerMember : outer ∈ tables)
    (outerLocal : state.locals.lookup (ofString "outer") = some (.val (.word outer)))
    (addrLocal : state.locals.lookup (ofString "addr") = some (.val (.word addr)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.rStruct [.val (.word a),.val (.word b),.val (.word c),.val (.word d)]))
    (mLocal : state.locals.lookup (ofString "m") = some (.rStruct [.val (.word (0 : BitVec 64)),.val (.word lookupValue)]))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (addrAligned : addr.toNat % 8 = 0) (keyAligned : key.toNat % 8 = 0)
    (addrWords : ∀ offset : Nat, offset < (widths outer).toNat → state.memaddrs (addr + BitVec.ofNat 64 offset))
    (addrBytes : ∀ offset : Nat, offset < (widths outer).toNat → state.memaddrs (panByteAlignHOL (addr + BitVec.ofNat 64 offset)))
    (keyWords : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (watched targets : Set (BitVec 64)) (watchedSubset : watched ⊆ tables)
    (registered : ∀ other ∈ watched, HashTableValuesIn other targets state)
    (saved : JournalSavedValuesIn journal count.toNat watched targets state)
    (ticks : 2 ^ 76 + 19 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state stateStorageInnerScope = (result,post) ∧
      state.clock ≤ post.clock + (2 ^ 76 + 19) ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) → TransactionRegistryWorld (withTableWidth widths pointer 32)
        (insert pointer tables) fieldPointer ts journal snapshot ((count + 1) + 1) post ∧
        (∀ other ∈ watched, HashTableValuesIn other (insert pointer targets) post) ∧
        JournalSavedValuesIn journal ((count + 1) + 1).toNat watched (insert pointer targets) post) := by
  let entered := setVarHOLFinite (ofString "inner") (.val (.word (0 : BitVec 64))) state
  have enteredValid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count entered := valid.after_read rfl rfl rfl rfl rfl
  have atInner : entered.locals.lookup (ofString "inner") = some (.val (.word (0 : BitVec 64))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have locals : ∀ name, name ≠ ofString "inner" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  obtain ⟨result,post,run,cost,remaining,noTimeout,preserved⟩ := enteredValid.storage_new_inner_all_requests_registered_values_in entered widths tables
    fieldPointer ts journal snapshot count pointer outer addr key a b c d 0 lookupValue outerMember atInner
    ((locals (ofString "outer") (by decide)).trans outerLocal) ((locals (ofString "addr") (by decide)).trans addrLocal)
    ((locals (ofString "key") (by decide)).trans keyLocal) ((locals (ofString "value") (by decide)).trans valueLocal)
    ((locals (ofString "m") (by decide)).trans mLocal) heap addrAligned keyAligned addrWords addrBytes keyWords keyBytes watched targets watchedSubset
      (fun other belongs => (registered other belongs).after_read rfl rfl rfl)
      (saved.after_frame (Nat.le_refl _) (by intro index inside offset belongs; rfl)) ticks
  have full : evaluateHOLFiniteState state stateStorageInnerScope =
      (let output := evaluateHOLFiniteState entered stateStorageInnerSelection;
        (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (ofString "inner",state.locals.lookup (ofString "inner"))})) := by
    unfold stateStorageInnerScope
    rw [evaluateHOLFiniteState_dec_total]
    simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
    rfl
  rw [run] at full
  dsimp only at full
  refine ⟨result,_,full,cost,remaining,noTimeout,?_⟩
  intro value success
  have joint := preserved value success
  exact ⟨joint.1.after_read rfl rfl rfl rfl rfl,
    (fun other belongs => (joint.2.1 other belongs).after_read rfl rfl rfl),
    joint.2.2.after_frame (Nat.le_refl _) (by intro index inside offset belongs; rfl)⟩

#print axioms TransactionRegistryWorld.storage_new_inner_all_requests_registered_values_in
#print axioms TransactionRegistryWorld.storage_new_inner_scope_all_requests_registered_values_in
end InitECandidate.Runtime
