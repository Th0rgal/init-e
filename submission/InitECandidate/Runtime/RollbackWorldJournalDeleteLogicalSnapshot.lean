import InitECandidate.Runtime.RollbackWorldJournalDeleteBody
import InitECandidate.Runtime.PanFreshLocalClock
import InitECandidate.Runtime.JournalDeleteSource32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem jdel_snapshot_fresh : ofString "snap" ∉ freeVarIdsHOL (sourceFunctionBody Guest.guestFn_jdel) := by
  rw [source_journalDelete32]
  simp [freeVarIdsHOL,varExpHOL,journalDeleteAfterGet32,journalDeletePresent32,journalDeleteCopy32,journalDeleteRecordSource32,journalDeleteFinish32]
  decide

/-- The snapshot is purely logical for jdel: no snap binding is required in
its actual source entry state, including actual function-call parameter locals. -/
theorem jdel_body_bounded_logical_snapshot {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {journal snapshot count : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (world : RollbackWorld widths tables journal snapshot count
      (setVarHOLFinite (ofString "snap") (.val (.word snapshot)) state))
    (separated : RollbackPhysicalSeparated widths tables state)
    (table key : BitVec 64) (member : table ∈ tables)
    (supported : widths table = 20 ∨ widths table = 32 ∨ widths table = 52)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (ticks : 2 ^ 43 ≤ state.clock)
    (journalBound : journal.toNat + 524288 * 32 ≤ 33806089496)
    (journalAligned : journal.toNat % 8 = 0)
    (journalHeaders : ∀ other ∈ tables, journal.toNat + 524288 * 32 ≤ other.toNat)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (capacityGlobal : state.globals.lookup (ofString "journal_cap") = some (.val (.word (524288 : BitVec 64)))) :
    state.clock ≤ (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jdel)).2.clock + 2 ^ 43 ∧
      (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jdel)).2.clock ≤ state.clock ∧
      (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jdel)).1 ≠ none ∧
      (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jdel)).1 ≠ some .timeOut := by
  let bound := setVarHOLFinite (ofString "snap") (.val (.word snapshot)) state
  have locals : ∀ name, name ≠ ofString "snap" → bound.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [bound,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have apart : RollbackPhysicalSeparated widths tables bound := separated.after_read rfl rfl rfl rfl rfl
  have bounded := world.jdel_body_bounded apart table key member supported
    ((locals (ofString "t") (by decide)).trans tableLocal) ((locals (ofString "key") (by decide)).trans keyLocal)
    keyAligned keyWords keyBytes ticks
    journalBound journalAligned journalHeaders heapDomain capacityGlobal
  obtain ⟨resultSame,clockSame⟩ := evaluate_fresh_local_result_clock state (ofString "snap") (.val (.word snapshot))
    (sourceFunctionBody Guest.guestFn_jdel) jdel_snapshot_fresh
  change (evaluateHOLFiniteState bound (sourceFunctionBody Guest.guestFn_jdel)).1 = _ at resultSame
  change (evaluateHOLFiniteState bound (sourceFunctionBody Guest.guestFn_jdel)).2.clock = _ at clockSame
  change bound.clock ≤ (evaluateHOLFiniteState bound (sourceFunctionBody Guest.guestFn_jdel)).2.clock + 2 ^ 43 ∧
    (evaluateHOLFiniteState bound (sourceFunctionBody Guest.guestFn_jdel)).2.clock ≤ bound.clock ∧
    (evaluateHOLFiniteState bound (sourceFunctionBody Guest.guestFn_jdel)).1 ≠ none ∧
    (evaluateHOLFiniteState bound (sourceFunctionBody Guest.guestFn_jdel)).1 ≠ some .timeOut at bounded
  rw [resultSame,clockSame] at bounded
  exact bounded

#print axioms jdel_snapshot_fresh
#print axioms jdel_body_bounded_logical_snapshot
end InitECandidate.Runtime
