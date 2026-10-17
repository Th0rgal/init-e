import InitECandidate.Runtime.RollbackWorldDeleteAppendExecutionFrame
import InitECandidate.Runtime.JournalRecordGeometry32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A full journal-buffer reservation discharges record arithmetic, field
accessibility and separation from every registered table for each append. -/
theorem RollbackWorld.evaluate_delete_record_append_reserved_frame {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
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
    (old : state.locals.lookup (ofString "old") = some (.rStruct [.val (.word present),.val (.word value)])) :
    ∃ post, (∀ continuation, evaluateHOLFiniteState state
      (journalDeleteRecordSource32 (.seq (.assign .global (ofString "journal_n")
        (.op .add [.var .global (ofString "journal_n"),.const 1])) continuation)) =
      evaluateHOLFiniteState post continuation) ∧
      RollbackWorld widths tables journal snapshot (count + 1) post ∧
      RollbackPhysicalSeparated widths tables post ∧ post.clock = state.clock ∧
      post.locals = state.locals ∧ post.memaddrs = state.memaddrs ∧ post.code = state.code ∧
      (∀ name, name ≠ ofString "journal_n" → post.globals.lookup name = state.globals.lookup name) := by
  have inside : count.toNat < (524288 : BitVec 64).toNat := space
  have capacityBound : journal.toNat + (524288 : BitVec 64).toNat * 32 ≤ 33806089496 := journalBound
  obtain ⟨recordAddress,_,recordEnd⟩ := journal_record_geometry32 journal count 524288 inside capacityBound journalAligned
  have fields := journal_record_domains32 state journal count 524288 inside capacityBound journalAligned
    (by intro address lower upper; apply heapDomain address; omega)
  have countWord : BitVec.ofNat 64 count.toNat = count := by simp
  apply world.evaluate_delete_record_append_frame separated table key present value member space
  · simpa only [countWord] using recordAddress
  · simpa only [countWord] using (show (journal + count * 32).toNat + 32 ≤ 33806089496 from by omega)
  · intro other belongs
    have header := journalHeaders other belongs
    simpa only [countWord] using (show (journal + count * 32).toNat + 32 ≤ other.toNat from by omega)
  · exact supported
  · simpa only [countWord] using fields
  · exact aligned
  · exact words
  · exact bytes
  · exact r
  · exact t
  · exact kc
  · exact old

#print axioms RollbackWorld.evaluate_delete_record_append_reserved_frame
end InitECandidate.Runtime
