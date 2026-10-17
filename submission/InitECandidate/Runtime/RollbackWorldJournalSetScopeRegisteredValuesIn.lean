import InitECandidate.Runtime.RollbackWorldJournalSetScope
import InitECandidate.Runtime.RollbackWorldJournalSetSuffixRegisteredValuesIn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful record-scope execution preserves the enlarged saved-value journal, including restoration of the temporary record pointer. -/
theorem RollbackWorld.journal_set_record_scope_registered_values_in {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {journal snapshot count : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (world : RollbackWorld widths tables journal snapshot count state)
    (separated : RollbackPhysicalSeparated widths tables state)
    (table key present value : BitVec 64) (member : table ∈ tables)
    (space : count.toNat < 524288)
    (journalBound : journal.toNat + 524288 * 32 ≤ 33806089496)
    (journalAligned : journal.toNat % 8 = 0)
    (journalHeaders : ∀ other ∈ tables, journal.toNat + 524288 * 32 ≤ other.toNat)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (supported : widths table = 20 ∨ widths table = 32 ∨ widths table = 52)
    (aligned : key.toNat % 8 = 0)
    (words : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (bytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (t : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (kc : state.locals.lookup (ofString "kc") = some (.val (.word key)))
    (old : state.locals.lookup (ofString "old") = some (.rStruct [.val (.word present),.val (.word value)]))
    (originalKey newValue : BitVec 64)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word originalKey)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word newValue)))
    (originalAligned : originalKey.toNat % 8 = 0)
    (originalWords : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (originalKey + BitVec.ofNat 64 offset))
    (originalBytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (originalKey + BitVec.ofNat 64 offset)))
    (ticks : 2 ^ 74 ≤ state.clock)
    (watched targets : Set (BitVec 64))
    (savedValues : JournalSavedValuesIn journal count.toNat watched targets state)
    (registered : table ∈ watched → present ≠ 0 → value ∈ targets)
    (watchedSubset : watched ⊆ tables)
    (tableValues : ∀ other ∈ watched, HashTableValuesIn other targets state)
    (newRegistered : table ∈ watched → newValue ∈ targets)
    (returnedValue : ValueHOL 64)
    (success : (evaluateHOLFiniteState state journalSetRecordScope32).1 = some (.returned returnedValue)) :
    JournalSavedValuesIn journal (count + 1).toNat watched targets (evaluateHOLFiniteState state journalSetRecordScope32).2 ∧
    (∀ other ∈ watched, HashTableValuesIn other targets (evaluateHOLFiniteState state journalSetRecordScope32).2) := by
  let entered := setVarHOLFinite (ofString "r") (.val (.word (journal + count * 32))) state
  have enteredWorld : RollbackWorld widths tables journal snapshot count entered :=
    world.after_read rfl rfl rfl rfl rfl (by
      simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "r" ≠ ofString "snap" from by decide])
  have enteredSep : RollbackPhysicalSeparated widths tables entered := separated.after_read rfl rfl rfl rfl rfl
  have atR : entered.locals.lookup (ofString "r") = some (.val (.word (journal + BitVec.ofNat 64 count.toNat * 32))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atT : entered.locals.lookup (ofString "t") = some (.val (.word table)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "r" ≠ ofString "t" from by decide] using t
  have atKc : entered.locals.lookup (ofString "kc") = some (.val (.word key)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "r" ≠ ofString "kc" from by decide] using kc
  have atOld : entered.locals.lookup (ofString "old") = some (.rStruct [.val (.word present),.val (.word value)]) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "r" ≠ ofString "old" from by decide] using old
  have atKey : entered.locals.lookup (ofString "key") = some (.val (.word originalKey)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "r" ≠ ofString "key" from by decide] using keyLocal
  have atValue : entered.locals.lookup (ofString "value") = some (.val (.word newValue)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "r" ≠ ofString "value" from by decide] using valueLocal
  have scopeRun : evaluateHOLFiniteState state journalSetRecordScope32 =
      (let output := evaluateHOLFiniteState entered (journalRecordSource32 journalSetFinish32);
        (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (ofString "r",state.locals.lookup (ofString "r"))})) :=
    evaluate_journal_record_scope32 state journal count _ world.journalGlobal world.counter
  have bodySuccess : (evaluateHOLFiniteState entered (journalRecordSource32 journalSetFinish32)).1 = some (.returned returnedValue) :=
    (congrArg Prod.fst scopeRun).symm.trans success
  have frame := enteredWorld.journal_set_suffix_registered_values_in enteredSep table key present value member space journalBound journalAligned journalHeaders heapDomain
    supported aligned words bytes atR atT atKc atOld originalKey newValue atKey atValue originalAligned originalWords originalBytes ticks watched targets (savedValues.after_frame (Nat.le_refl _) (by intro index inside offset belongs; rfl)) registered watchedSubset (fun other belongs => (tableValues other belongs).after_read rfl rfl rfl) newRegistered returnedValue bodySuccess
  rw [scopeRun]
  exact ⟨frame.1.after_frame (Nat.le_refl _) (by intro index inside offset belongs; rfl),
    (fun other belongs => (frame.2 other belongs).after_read rfl rfl rfl)⟩

#print axioms RollbackWorld.journal_set_record_scope_registered_values_in
end InitECandidate.Runtime
