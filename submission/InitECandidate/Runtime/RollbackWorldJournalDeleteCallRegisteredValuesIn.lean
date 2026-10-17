import InitECandidate.Runtime.RollbackWorldJournalDeleteCall
import InitECandidate.Runtime.RollbackWorldJournalDeleteLogicalRegisteredValuesIn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An actual successful jdel call preserves saved undo values after caller-local restoration. -/
theorem rollback_world_jdel_call_registered_values_in {F : Type} (state : PanSemStateFiniteExact 64 F)
    (widths : BitVec 64 → BitVec 64) (tables : Set (BitVec 64))
    (journal snapshot count table key : BitVec 64)
    (world : RollbackWorld widths tables journal snapshot count (setVarHOLFinite (ofString "snap") (.val (.word snapshot)) state))
    (separated : RollbackPhysicalSeparated widths tables state)
    (member : table ∈ tables) (supported : widths table = 20 ∨ widths table = 32 ∨ widths table = 52)
    (tableArgument keyArgument : ExpHOL 64)
    (arguments : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [tableArgument,keyArgument] = some [.val (.word table),.val (.word key)])
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (ticks : 2 ^ 43 + 1 ≤ state.clock)
    (journalBound : journal.toNat + 524288 * 32 ≤ 33806089496)
    (journalAligned : journal.toNat % 8 = 0)
    (journalHeaders : ∀ other ∈ tables, journal.toNat + 524288 * 32 ≤ other.toNat)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (capacityGlobal : state.globals.lookup (ofString "journal_cap") = some (.val (.word (524288 : BitVec 64))))
    (code : state.code = originalRuntimeCode)
    (watched targets : Set (BitVec 64)) (watchedSubset : watched ⊆ tables)
    (tableValues : ∀ table ∈ watched, HashTableValuesIn table targets state)
    (savedValues : JournalSavedValuesIn journal count.toNat watched targets state)
    (success : (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jdel") [tableArgument,keyArgument])).1 = none) :
    ∃ next : BitVec 64, (next = count ∨ next = count + 1) ∧
      JournalSavedValuesIn journal next.toNat watched targets
        (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jdel") [tableArgument,keyArgument])).2 ∧
      (∀ other ∈ watched, HashTableValuesIn other targets (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jdel") [tableArgument,keyArgument])).2) ∧
      (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "jdel") [tableArgument,keyArgument])).2.globals.lookup (ofString "journal_n") = some (.val (.word next)) := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) :=
    (HolFiniteMapExact.empty.update (ofString "t",.val (.word table))).update (ofString "key",.val (.word key))
  let entry := callEntryStateHOLFinite state callee
  let logicalEntry := setVarHOLFinite (ofString "snap") (.val (.word snapshot)) entry
  have entryWorld : RollbackWorld widths tables journal snapshot count logicalEntry := world.after_read rfl rfl rfl rfl rfl (by
    simp [logicalEntry,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  have entrySep : RollbackPhysicalSeparated widths tables entry := separated.after_read rfl rfl rfl rfl rfl
  have t : entry.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "key" ≠ ofString "t" from by decide]
  have k : entry.locals.lookup (ofString "key") = some (.val (.word key)) := by
    simp [entry,callEntryStateHOLFinite,callee,HolFiniteMapExact.lookup_update,FUPDATE]
  have preserves : ∀ returnedValue, (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_jdel)).1 = some (.returned returnedValue) →
      ∃ next : BitVec 64, (next = count ∨ next = count + 1) ∧
      JournalSavedValuesIn journal next.toNat watched targets (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_jdel)).2 ∧
      (∀ other ∈ watched, HashTableValuesIn other targets (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_jdel)).2) ∧
      (evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_jdel)).2.globals.lookup (ofString "journal_n") = some (.val (.word next)) := by
    intro returnedValue returned
    exact jdel_body_registered_values_in_logical_snapshot entryWorld entrySep table key member supported t k keyAligned keyWords keyBytes
      (by change 2 ^ 43 ≤ state.clock - 1; omega) journalBound journalAligned journalHeaders heapDomain capacityGlobal watched targets watchedSubset
        (by intro other belongs; exact (tableValues other belongs).after_read rfl rfl rfl)
        (savedValues.after_frame (Nat.le_refl _) (by intro index inside offset belongs; rfl)) returnedValue returned
  have installed : state.code.lookup (ofString "jdel") = some ([(ofString "t",.one),(ofString "key",.one)],sourceFunctionBody Guest.guestFn_jdel,.one) := by
    rw [code]; exact originalRuntimeCode_journalDelete_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "jdel") (ofString "t") (ofString "key")
    (sourceFunctionBody Guest.guestFn_jdel) table key (by decide) installed
  simp only [evaluateHOLFiniteState_call,arguments] at success ⊢
  rw [lookup] at success ⊢
  dsimp only at success ⊢
  have clock : state.clock ≠ 0 := by omega
  simp only [if_neg clock] at success ⊢
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_jdel) with
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
                obtain ⟨next,counts,valid,postValues,postCounter⟩ := preserves returnedValue rfl
                exact ⟨next,counts,valid.after_frame (Nat.le_refl _) (by intro index inside offset belongs; rfl),
    (fun other belongs => (postValues other belongs).after_read rfl rfl rfl),postCounter⟩
              · cases success
          | _ => cases success

#print axioms rollback_world_jdel_call_registered_values_in
end InitECandidate.Runtime
