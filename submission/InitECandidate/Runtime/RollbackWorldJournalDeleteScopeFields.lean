import InitECandidate.Runtime.RollbackWorldJournalDeleteSuffixFields
import InitECandidate.Runtime.RollbackWorldJournalDeleteScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual scoped deletion record block returns with an enlarged separated
rollback world and costs at most the uniform deletion clock ceiling. -/
theorem RollbackWorld.journal_delete_record_scope_bounded_fields {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
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
    (originalKey : BitVec 64)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word originalKey)))
    (originalAligned : originalKey.toNat % 8 = 0)
    (originalWords : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (originalKey + BitVec.ofNat 64 offset))
    (originalBytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (originalKey + BitVec.ofNat 64 offset)))
    (ts fieldPointer : BitVec 64)
    (tsFields : StateFreshTxFields ts fieldPointer stateFreshTxAllTables state)
    (tsBound : ts.toNat + 72 ≤ 33806089496)
    (journalBeforeTs : journal.toNat + 524288 * 32 ≤ ts.toNat)
    (headerBefore : ts.toNat + 72 ≤ table.toNat)
    (ticks : 2 ^ 42 ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state journalDeleteRecordScope32 =
      (some (.returned (.val (.word (0 : BitVec 64)))),
        {emptyLocalsHOLFinite post with locals := HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite post).locals (ofString "r",state.locals.lookup (ofString "r"))}) ∧
      RollbackWorld widths tables journal snapshot (count + 1) post ∧ RollbackPhysicalSeparated widths tables post ∧
      state.clock ≤ post.clock + 2 ^ 42 ∧ post.clock ≤ state.clock ∧
      (∀ name, name ≠ ofString "heap_ptr" → name ≠ ofString "journal_n" → post.globals.lookup name = state.globals.lookup name) ∧ StateFreshTxFields ts fieldPointer stateFreshTxAllTables post := by
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
  obtain ⟨post,run,nextWorld,nextSep,cost,remaining,globals,postFields⟩ := enteredWorld.journal_delete_suffix_bounded_fields enteredSep table key present value member space journalBound journalAligned journalHeaders heapDomain
    supported aligned words bytes atR atT atKc atOld originalKey atKey originalAligned originalWords originalBytes ts fieldPointer (tsFields.after_memory rfl) tsBound journalBeforeTs headerBefore ticks
  refine ⟨post,?_,nextWorld,nextSep,cost,remaining,globals,postFields⟩
  unfold journalDeleteRecordScope32
  rw [evaluate_journal_record_scope32 state journal count _ world.journalGlobal world.counter]
  change (let output := evaluateHOLFiniteState entered (journalDeleteRecordSource32 journalDeleteFinish32); _) = _
  rw [run]

#print axioms RollbackWorld.journal_delete_record_scope_bounded_fields
end InitECandidate.Runtime
