import InitECandidate.Runtime.RollbackWorldDeleteAppendReservedFields
import InitECandidate.Runtime.RollbackWorldRegisteredDeleteFields
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Original deletion record stores, increment, table deletion and return
establish the enlarged separated world with a uniform source-clock bound. -/
theorem RollbackWorld.journal_delete_suffix_bounded_fields {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
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
    (r : state.locals.lookup (ofString "r") = some (.val (.word (journal + BitVec.ofNat 64 count.toNat * 32))))
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
    ∃ post, evaluateHOLFiniteState state (journalDeleteRecordSource32 journalDeleteFinish32) =
      (some (.returned (.val (.word (0 : BitVec 64)))),emptyLocalsHOLFinite post) ∧
      RollbackWorld widths tables journal snapshot (count + 1) post ∧ RollbackPhysicalSeparated widths tables post ∧
      state.clock ≤ post.clock + 2 ^ 42 ∧ post.clock ≤ state.clock ∧
      (∀ name, name ≠ ofString "heap_ptr" → name ≠ ofString "journal_n" → post.globals.lookup name = state.globals.lookup name) ∧ StateFreshTxFields ts fieldPointer stateFreshTxAllTables post := by
  obtain ⟨middle,appendRun,midWorld,midSep,clock,locals,domain,code,midGlobals,midFields⟩ :=
    world.evaluate_delete_record_append_reserved_fields separated table key present value member space journalBound journalAligned journalHeaders heapDomain
      supported aligned words bytes r t kc old ts fieldPointer tsFields tsBound journalBeforeTs
  have args : evalListHOLFinite middle (h := fun address => Classical.propDecidable (middle.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key")] = some [.val (.word table),.val (.word originalKey)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,locals,t,keyLocal]
  obtain ⟨post,run,nextWorld,nextSep,cost,remaining,postGlobals,postFields⟩ := RollbackWorld.registered_delete_bounded_fields middle widths tables journal snapshot (count + 1) table originalKey midWorld midSep member
    supported ts fieldPointer midFields headerBefore (by omega) (.var .local (ofString "t")) (.var .local (ofString "key")) args originalAligned
    (by simpa only [domain] using originalWords) (by simpa only [domain] using originalBytes)
  refine ⟨post,?_,nextWorld,nextSep,by omega,by omega,?_,postFields⟩
  · change evaluateHOLFiniteState state (journalDeleteRecordSource32 (.seq (.assign .global (ofString "journal_n")
      (.op .add [.var .global (ofString "journal_n"),.const 1])) _)) = _
    rw [appendRun,evaluateHOLFiniteState_seq_line780,run]
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact]
  · intro name notHeap notCounter
    exact (congrArg (fun map => map.lookup name) postGlobals).trans (midGlobals name notCounter)

#print axioms RollbackWorld.journal_delete_suffix_bounded_fields
end InitECandidate.Runtime
