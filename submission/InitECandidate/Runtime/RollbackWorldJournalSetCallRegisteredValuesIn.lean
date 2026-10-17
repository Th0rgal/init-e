import InitECandidate.Runtime.RollbackWorldJournalSetCall
import InitECandidate.Runtime.RollbackWorldJournalSetLogicalRegisteredValuesIn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An actual successful discarded jset call preserves the enlarged saved-value journal after caller-local restoration. -/
theorem rollback_world_jset_call_registered_values_in {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (journal snapshot count table key value : BitVec 64)
    (world : RollbackWorld widths tables journal snapshot count (setVarHOLFinite (ofString "snap") (.val (.word snapshot)) state))
    (separated : RollbackPhysicalSeparated widths tables state)
    (member : table ∈ tables) (supported : widths table = 20 ∨ widths table = 32 ∨ widths table = 52)
    (tableArgument keyArgument valueArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument,valueArgument] = some [.val (.word table),.val (.word key),.val (.word value)])
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (ticks : 2 ^ 75 + 1 ≤ state.clock)
    (journalBound : journal.toNat + 524288 * 32 ≤ 33806089496)
    (journalAligned : journal.toNat % 8 = 0)
    (journalHeaders : ∀ other ∈ tables, journal.toNat + 524288 * 32 ≤ other.toNat)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (capacityGlobal : state.globals.lookup (ofString "journal_cap") = some (.val (.word (524288 : BitVec 64))))
    (code : state.code = originalRuntimeCode)
    (watched targets : Set (BitVec 64)) (watchedSubset : watched ⊆ tables)
    (tableValues : ∀ table ∈ watched, HashTableValuesIn table targets state)
    (savedValues : JournalSavedValuesIn journal count.toNat watched targets state)
    (newRegistered : table ∈ watched → value ∈ targets)
    (success : (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jset") [tableArgument,keyArgument,valueArgument])).1 = none) :
    JournalSavedValuesIn journal (count + 1).toNat watched targets
      (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jset") [tableArgument,keyArgument,valueArgument])).2 ∧
    (∀ other ∈ watched, HashTableValuesIn other targets
      (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jset") [tableArgument,keyArgument,valueArgument])).2) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    ((HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update (ofString "key",.val (.word key))).update (ofString "value",.val (.word value))
  let entry := callEntryStateHOLFinite state callee
  let logicalEntry := setVarHOLFinite (ofString "snap") (.val (.word snapshot)) entry
  have entryWorld : RollbackWorld widths tables journal snapshot count logicalEntry := world.after_read rfl rfl rfl rfl rfl (by
    simp [logicalEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  have entrySep : RollbackPhysicalSeparated widths tables entry := separated.after_read rfl rfl rfl rfl rfl
  have t : entry.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "value" ≠ ofString "t" from by decide,show ofString "key" ≠ ofString "t" from by decide]
  have k : entry.locals.lookup (ofString "key") = some (.val (.word key)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "value" ≠ ofString "key" from by decide]
  have v : entry.locals.lookup (ofString "value") = some (.val (.word value)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have preserves : ∀ returnedValue, (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_jset)).1 = some (.returned returnedValue) →
      JournalSavedValuesIn journal (count + 1).toNat watched targets (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_jset)).2 ∧
      (∀ other ∈ watched, HashTableValuesIn other targets (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_jset)).2) := by
    intro returnedValue returned
    exact jset_body_registered_values_in_logical_snapshot entryWorld entrySep table key value member supported t k v keyAligned keyWords keyBytes
      (by change 2 ^ 75 ≤ state.clock - 1; omega) journalBound journalAligned journalHeaders heapDomain capacityGlobal watched targets watchedSubset (by intro other belongs; exact (tableValues other belongs).after_read rfl rfl rfl)
        (savedValues.after_frame (Nat.le_refl _) (by intro index inside offset belongs; rfl)) newRegistered returnedValue returned
  have installed : state.code.lookup (ofString "jset") = some ([(ofString "t",.one),(ofString "key",.one),(ofString "value",.one)],sourceFunctionBody Guest.guestFn_jset,.one) := by
    rw [code]; exact originalRuntimeCode_journalSet_lookup
  have lookup := pan_three_word_lookup state.code.lookup (ofString "jset") (ofString "t") (ofString "key") (ofString "value")
    (sourceFunctionBody Guest.guestFn_jset) table key value (by decide) (by decide) (by decide) installed
  simp only [evaluateHOLFiniteState_call,arguments] at success ⊢
  rw [lookup] at success ⊢
  dsimp only at success ⊢
  have clock : state.clock ≠ 0 := by omega
  simp only [if_neg clock] at success ⊢
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_jset) with
  | mk result post =>
      rw [bodyRun] at success preserves
      cases result with
      | none => cases success
      | some result =>
          cases result with
          | returned returnedValue =>
              dsimp only at success ⊢
              split at success
              · rename_i goodShape
                simp only [goodShape,if_true]
                have valid := preserves returnedValue rfl
                exact ⟨valid.1.after_frame (Nat.le_refl _) (by intro index inside offset belongs; rfl),
                  (fun other belongs => (valid.2 other belongs).after_read rfl rfl rfl)⟩
              · cases success
          | _ => cases success

#print axioms rollback_world_jset_call_registered_values_in
end InitECandidate.Runtime
