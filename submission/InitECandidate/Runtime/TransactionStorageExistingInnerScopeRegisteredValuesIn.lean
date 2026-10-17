import InitECandidate.Runtime.TransactionStorageExistingInnerRegisteredValuesIn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original inner=0 declaration, existing-inner selection and update tail
retain the registry on successful return after restoring the caller's inner local. -/
theorem TransactionRegistryWorld.storage_existing_inner_scope_registered_values_in {F : Type}
    (state : PanSemStateFiniteExact 64 F) (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (fieldPointer ts journal snapshot count pointer inner key a b c d present : BitVec 64)
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (member : inner ∈ tables)
    (mLocal : state.locals.lookup (ofString "m") = some (.rStruct [.val (.word present),.val (.word inner)]))
    (nonzero : present ≠ 0)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.rStruct [.val (.word a),.val (.word b),.val (.word c),.val (.word d)]))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (widths inner).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (widths inner).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (watched targets : Set (BitVec 64)) (watchedSubset : watched ⊆ tables)
    (registered : ∀ other ∈ watched, HashTableValuesIn other targets state)
    (saved : JournalSavedValuesIn journal count.toNat watched targets state)
    (newRegistered : inner ∈ watched → pointer ∈ targets)
    (ticks : 2 ^ 75 + 2 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state stateStorageInnerScope = (result,post) ∧
      state.clock ≤ post.clock + (2 ^ 75 + 2) ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) → TransactionRegistryWorld widths tables fieldPointer ts journal snapshot (count + 1) post ∧
        (∀ other ∈ watched, HashTableValuesIn other targets post) ∧ JournalSavedValuesIn journal (count + 1).toNat watched targets post) := by
  let entered := setVarHOLFinite (ofString "inner") (.val (.word (0 : BitVec 64))) state
  have enteredValid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count entered := valid.after_read rfl rfl rfl rfl rfl
  have atInner : entered.locals.lookup (ofString "inner") = some (.val (.word (0 : BitVec 64))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atM : entered.locals.lookup (ofString "m") = some (.rStruct [.val (.word present),.val (.word inner)]) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "inner" ≠ ofString "m" from by decide] using mLocal
  have atKey : entered.locals.lookup (ofString "key") = some (.val (.word key)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "inner" ≠ ofString "key" from by decide] using keyLocal
  have atValue : entered.locals.lookup (ofString "value") = some (.rStruct [.val (.word a),.val (.word b),.val (.word c),.val (.word d)]) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "inner" ≠ ofString "value" from by decide] using valueLocal
  obtain ⟨result,post,run,cost,remaining,noTimeout,preserved⟩ := enteredValid.storage_existing_inner_registered_values_in entered widths tables fieldPointer ts journal snapshot count pointer inner key a b c d present 0
    member atInner atM nonzero atKey atValue heap keyAligned keyWords keyBytes watched targets watchedSubset
      (fun other belongs => (registered other belongs).after_read rfl rfl rfl)
      (saved.after_frame (Nat.le_refl _) (by intro index inside offset belongs; rfl)) newRegistered ticks
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

#print axioms TransactionRegistryWorld.storage_existing_inner_scope_registered_values_in
end InitECandidate.Runtime
