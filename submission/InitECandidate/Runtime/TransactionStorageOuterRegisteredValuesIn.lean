import InitECandidate.Runtime.TransactionStorageLookupRegisteredValuesIn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def stateStorageOuterScope : ProgHOL 64 :=
  .dec (ofString "outer") .one (.load .one (.op .add [.var .global (ofString "ts"),.const 32])) stateStorageLookupScope

theorem source_setStorage_outer_scope :
    stateInitSpineDrop 2 (sourceFunctionBody Guest.guestFn_set_storage) = stateStorageOuterScope := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The actual outer-table field load and its local scope preserve the typed
pointer invariant established by the storage lookup and update suffix. -/
theorem TransactionRegistryWorld.storage_outer_registered_values_in {F : Type}
    (state : PanSemStateFiniteExact 64 F) (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (fieldPointer ts journal snapshot count outer addr key a b c d : BitVec 64)
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (watched targets : Set (BitVec 64)) (watchedSubset : watched ⊆ tables) (targetsSubset : targets ⊆ tables)
    (typed : ∀ inner ∈ targets, widths inner = 32 ∧ inner ∉ watched)
    (outerWatched : outer ∈ watched)
    (registered : ∀ other ∈ watched, HashTableValuesIn other targets state)
    (saved : JournalSavedValuesIn journal count.toNat watched targets state)
    (binding : (32,outer) ∈ stateFreshTxTableBindings fieldPointer stateFreshTxAllTables)
    (addrLocal : state.locals.lookup (ofString "addr") = some (.val (.word addr)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.rStruct [.val (.word a),.val (.word b),.val (.word c),.val (.word d)]))
    (addrAligned : addr.toNat % 8 = 0) (keyAligned : key.toNat % 8 = 0)
    (addrWords : ∀ offset : Nat, offset < (widths outer).toNat → state.memaddrs (addr + BitVec.ofNat 64 offset))
    (addrBytes : ∀ offset : Nat, offset < (widths outer).toNat → state.memaddrs (panByteAlignHOL (addr + BitVec.ofNat 64 offset)))
    (keyWords : ∀ offset : Nat, offset < 32 → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < 32 → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (ticks : 2 ^ 77 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state stateStorageOuterScope = (result,post) ∧
      state.clock ≤ post.clock + 2 ^ 77 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (∀ value, result = some (.returned value) → ∃ nextWidths nextTables nextTargets nextCount,
        TransactionRegistryWorld nextWidths nextTables fieldPointer ts journal snapshot nextCount post ∧
        watched ⊆ nextTables ∧ nextTargets ⊆ nextTables ∧
        (∀ inner ∈ nextTargets, nextWidths inner = 32 ∧ inner ∉ watched) ∧
        (∀ other ∈ watched, HashTableValuesIn other nextTargets post) ∧
        JournalSavedValuesIn journal nextCount.toNat watched nextTargets post) := by
  let entered := setVarHOLFinite (ofString "outer") (.val (.word outer)) state
  have enteredValid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count entered := valid.after_read rfl rfl rfl rfl rfl
  have atOuter : entered.locals.lookup (ofString "outer") = some (.val (.word outer)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have other : ∀ name, name ≠ ofString "outer" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  obtain ⟨result,post,run,cost,remaining,noTimeout,preserved⟩ := enteredValid.storage_lookup_registered_values_in entered widths tables
    fieldPointer ts journal snapshot count outer addr key a b c d watched targets watchedSubset targetsSubset typed outerWatched
    (fun other belongs => (registered other belongs).after_read rfl rfl rfl)
    (saved.after_frame (Nat.le_refl _) (by intro index inside offset belongs; rfl)) atOuter
    ((other _ (by decide)).trans addrLocal) ((other _ (by decide)).trans keyLocal) ((other _ (by decide)).trans valueLocal)
    addrAligned keyAligned addrWords addrBytes keyWords keyBytes ticks
  have loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (.op .add [.var .global (ofString "ts"),.const 32])) = some (.val (.word outer)) :=
    (valid.load_registered state widths tables fieldPointer ts journal snapshot count 32 outer binding).1
  have full : evaluateHOLFiniteState state stateStorageOuterScope =
      (result,{post with locals := HolFiniteMapExact.resVarEq post.locals (ofString "outer",state.locals.lookup (ofString "outer"))}) := by
    unfold stateStorageOuterScope
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    rw [loaded]
    dsimp only
    have shape : shapeEqHOL .one (shapeOfHOLExact (.val (.word outer))) = true := by simp [shapeEqHOL,shapeOfHOLExact]
    rw [if_pos shape,run]
  refine ⟨result,_,full,cost,remaining,noTimeout,?_⟩
  intro value success
  obtain ⟨nextWidths,nextTables,nextTargets,nextCount,world,watchedIn,targetsIn,nextTyped,valuesIn,savedIn⟩ := preserved value success
  exact ⟨nextWidths,nextTables,nextTargets,nextCount,world.after_read rfl rfl rfl rfl rfl,watchedIn,targetsIn,nextTyped,
    (fun other belongs => (valuesIn other belongs).after_read rfl rfl rfl),
    savedIn.after_frame (Nat.le_refl _) (by intro index inside offset belongs; rfl)⟩

#print axioms source_setStorage_outer_scope
#print axioms TransactionRegistryWorld.storage_outer_registered_values_in
end InitECandidate.Runtime
