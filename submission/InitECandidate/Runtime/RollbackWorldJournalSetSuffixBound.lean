import InitECandidate.Runtime.RollbackWorldJournalSetSuffix
import InitECandidate.Runtime.RollbackWorldRegisteredSetBound
import InitECandidate.Runtime.PanSequenceReturnBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The journal record/set/return suffix has a uniform source-clock bound,
including terminal allocation failures, independently of collision patterns. -/
theorem RollbackWorld.journal_set_suffix_bounded {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
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
    (originalKey newValue : BitVec 64)
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word originalKey)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word newValue)))
    (originalAligned : originalKey.toNat % 8 = 0)
    (originalWords : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (originalKey + BitVec.ofNat 64 offset))
    (originalBytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (originalKey + BitVec.ofNat 64 offset)))
    (ticks : 2 ^ 72 ≤ state.clock) :
    state.clock ≤ (evaluateHOLFiniteState state (journalRecordSource32 journalSetFinish32)).2.clock + 2 ^ 72 ∧
      (evaluateHOLFiniteState state (journalRecordSource32 journalSetFinish32)).2.clock ≤ state.clock := by
  obtain ⟨middle,appendRun,midWorld,midSep,clock,locals,domain,code⟩ :=
    world.evaluate_record_append_reserved separated table key present value member space journalBound journalAligned journalHeaders heapDomain
      supported aligned words bytes r t kc old
  let call : ProgHOL 64 := .call (some (none,none)) (ofString "htab_set")
    [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")]
  have args : evalListHOLFinite middle (h := fun address => Classical.propDecidable (middle.memaddrs address))
      [.var .local (ofString "t"),.var .local (ofString "key"),.var .local (ofString "value")] =
      some [.val (.word table),.val (.word originalKey),.val (.word newValue)] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,locals,t,keyLocal,valueLocal]
  have suffixRun : evaluateHOLFiniteState state (journalRecordSource32 journalSetFinish32) =
      evaluateHOLFiniteState middle (.seq call (.return (.const 0))) := appendRun _
  have bounded := RollbackWorld.registered_set_bounded middle widths tables journal snapshot (count + 1) table originalKey newValue midWorld midSep member
    supported (by omega) (by intro address upper; rw [domain]; exact heapDomain address upper)
    (.var .local (ofString "t")) (.var .local (ofString "key")) (.var .local (ofString "value")) args originalAligned
    (by simpa only [domain] using originalWords) (by simpa only [domain] using originalBytes)
  change middle.clock ≤ (evaluateHOLFiniteState middle call).2.clock + 2 ^ 72 ∧
    (evaluateHOLFiniteState middle call).2.clock ≤ middle.clock at bounded
  have returned := (evaluate_sequence_return_zero middle call).1
  rw [suffixRun]
  rw [returned]
  exact ⟨by omega,by omega⟩

#print axioms RollbackWorld.journal_set_suffix_bounded
end InitECandidate.Runtime
