import InitECandidate.Runtime.RollbackWorldJournalDeleteBodySuccess
import InitECandidate.Runtime.PanFreshLocalStateFrame
import InitECandidate.Runtime.RollbackWorldJournalDeleteLogicalSnapshot
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful body preservation with snapshot solely in the invariant,
retaining the actual returned state's memory and global metadata. -/
theorem jdel_body_success_logical_snapshot {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
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
    (capacityGlobal : state.globals.lookup (ofString "journal_cap") = some (.val (.word (524288 : BitVec 64))))
    (returnedValue : ValueHOL 64)
    (success : (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jdel)).1 = some (.returned returnedValue)) :
    ∃ next : BitVec 64, (next = count ∨ next = count + 1) ∧
      RollbackWorld widths tables journal snapshot next
      (setVarHOLFinite (ofString "snap") (.val (.word snapshot)) (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jdel)).2) ∧
      RollbackPhysicalSeparated widths tables (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jdel)).2 := by
  let bound := setVarHOLFinite (ofString "snap") (.val (.word snapshot)) state
  have locals : ∀ name, name ≠ ofString "snap" → bound.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [bound,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have apart : RollbackPhysicalSeparated widths tables bound := separated.after_read rfl rfl rfl rfl rfl
  obtain ⟨resultSame,frame⟩ := evaluate_fresh_local_nonlocal_state state (ofString "snap") (.val (.word snapshot))
    (sourceFunctionBody Guest.guestFn_jdel) jdel_snapshot_fresh
  have shadowSuccess : (evaluateHOLFiniteState bound (sourceFunctionBody Guest.guestFn_jdel)).1 = some (.returned returnedValue) := resultSame.trans success
  obtain ⟨next,counts,valid,postApart⟩ := world.jdel_body_success apart table key member supported
    ((locals (ofString "t") (by decide)).trans tableLocal) ((locals (ofString "key") (by decide)).trans keyLocal)
    keyAligned keyWords keyBytes ticks
    journalBound journalAligned journalHeaders heapDomain capacityGlobal returnedValue shadowSuccess
  have memory := congrArg (fun s : PanSemStateFiniteExact 64 F => s.memory) frame.symm
  have globals := congrArg (fun s : PanSemStateFiniteExact 64 F => s.globals) frame.symm
  have code := congrArg (fun s : PanSemStateFiniteExact 64 F => s.code) frame.symm
  have domain := congrArg (fun s : PanSemStateFiniteExact 64 F => s.memaddrs) frame.symm
  have endian := congrArg (fun s : PanSemStateFiniteExact 64 F => s.be) frame.symm
  exact ⟨next,counts,valid.after_logical_frame memory globals code domain endian,postApart.after_read memory globals code domain endian⟩

#print axioms jdel_body_success_logical_snapshot
end InitECandidate.Runtime
