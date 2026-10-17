import InitECandidate.Runtime.StateStorageInnerSelection
import InitECandidate.Runtime.RegistryTableSetLogicalRegisteredValuesIn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def stateAccountReadTrack : ProgHOL 64 :=
  .call (some (none,none)) (ofString "htab_set")
    [.load .one (.op .add [.var .global (ofString "ts"),.const 8]),.var .local (ofString "addr"),.const 1]

theorem source_getAccountOptional_read_prefix :
    sourceFunctionBody Guest.guestFn_get_account_optional = .seq stateAccountReadTrack
      (stateInitSpineDrop 1 (sourceFunctionBody Guest.guestFn_get_account_optional)) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_getPreStateAccountOptional_read_prefix :
    sourceFunctionBody Guest.guestFn_get_pre_state_account_optional = .seq stateAccountReadTrack
      (stateInitSpineDrop 1 (sourceFunctionBody Guest.guestFn_get_pre_state_account_optional)) := by
  unfold sourceFunctionBody
  rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The shared account-read tracking prefix preserves the pointer invariants
without journaling its numeric read marker. -/
theorem TransactionRegistryWorld.mark_account_read_registered_values_in {F : Type}
    (state : PanSemStateFiniteExact 64 F) (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (fieldPointer ts journal snapshot count table key : BitVec 64)
    (valid : TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count state)
    (binding : (8,table) ∈ stateFreshTxTableBindings fieldPointer stateFreshTxAllTables)
    (addrLocal : state.locals.lookup (ofString "addr") = some (.val (.word key)))
    (aligned : key.toNat % 8 = 0)
    (words : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (watched targets : Set (BitVec 64)) (watchedSubset : watched ⊆ tables)
    (registered : ∀ other ∈ watched, HashTableValuesIn other targets state)
    (saved : JournalSavedValuesIn journal count.toNat watched targets state)
    (readUnwatched : table ∉ watched)
    (ticks : 2 ^ 74 ≤ state.clock) :
    let output := evaluateHOLFiniteState state stateAccountReadTrack;
    output.1 ≠ some .timeOut ∧ state.clock ≤ output.2.clock + 2 ^ 74 ∧ output.2.clock ≤ state.clock ∧
      (output.1 = none → TransactionRegistryWorld widths tables fieldPointer ts journal snapshot count output.2 ∧
        (∀ other ∈ watched, HashTableValuesIn other targets output.2) ∧ JournalSavedValuesIn journal count.toNat watched targets output.2) := by
  have loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (.op .add [.var .global (ofString "ts"),.const 8])) = some (.val (.word table)) :=
    (valid.load_registered state widths tables fieldPointer ts journal snapshot count 8 table binding).1
  let shadow := setVarHOLFinite (ofString "snap") (.val (.word snapshot)) state
  have shadowLoaded : @evalHOLExact 64 F _ shadow.toExact
      (fun address => Classical.propDecidable (shadow.memaddrs address))
      (.load .one (.op .add [.var .global (ofString "ts"),.const 8])) = some (.val (.word table)) := loaded
  have addr : shadow.locals.lookup (ofString "addr") = some (.val (.word key)) := by
    simpa [shadow,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "snap" ≠ ofString "addr" from by decide] using addrLocal
  have args : evalListHOLFinite shadow (h := fun address => Classical.propDecidable (shadow.memaddrs address))
      [.load .one (.op .add [.var .global (ofString "ts"),.const 8]),.var .local (ofString "addr"),.const 1] =
      some [.val (.word table),.val (.word key),.val (.word (1 : BitVec 64))] := by
    simp only [evalListHOLFinite,evalListHOLExact]
    rw [shadowLoaded]
    simp [evalHOLExact,addr]
  exact valid.table_set_logical_registered_values_in state widths tables fieldPointer ts journal snapshot count table key 1
    (valid.load_registered state widths tables fieldPointer ts journal snapshot count 8 table binding).2 _ _ _ args aligned words bytes
    watched targets watchedSubset registered saved (fun belongs => False.elim (readUnwatched belongs)) (by simp [freeVarIdsHOL,varExpHOL]; decide) ticks

#print axioms source_getAccountOptional_read_prefix
#print axioms source_getPreStateAccountOptional_read_prefix
#print axioms TransactionRegistryWorld.mark_account_read_registered_values_in
end InitECandidate.Runtime
