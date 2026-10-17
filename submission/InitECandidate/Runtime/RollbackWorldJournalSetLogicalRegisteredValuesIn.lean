import InitECandidate.Runtime.RollbackWorldJournalSetBodyRegisteredValuesIn
import InitECandidate.Runtime.PanFreshLocalStateFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Full jset saved-value journal preservation with snapshot carried solely in the invariant. -/
theorem jset_body_registered_values_in_logical_snapshot {F : Type} {widths : BitVec 64 → BitVec 64} {tables : Set (BitVec 64)}
    {journal snapshot count : BitVec 64} {state : PanSemStateFiniteExact 64 F}
    (world : RollbackWorld widths tables journal snapshot count
      (setVarHOLFinite (ofString "snap") (.val (.word snapshot)) state))
    (separated : RollbackPhysicalSeparated widths tables state)
    (table key value : BitVec 64) (member : table ∈ tables)
    (supported : widths table = 20 ∨ widths table = 32 ∨ widths table = 52)
    (tableLocal : state.locals.lookup (ofString "t") = some (.val (.word table)))
    (keyLocal : state.locals.lookup (ofString "key") = some (.val (.word key)))
    (valueLocal : state.locals.lookup (ofString "value") = some (.val (.word value)))
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < (widths table).toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset)))
    (ticks : 2 ^ 75 ≤ state.clock)
    (journalBound : journal.toNat + 524288 * 32 ≤ 33806089496)
    (journalAligned : journal.toNat % 8 = 0)
    (journalHeaders : ∀ other ∈ tables, journal.toNat + 524288 * 32 ≤ other.toNat)
    (heapDomain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (capacityGlobal : state.globals.lookup (ofString "journal_cap") = some (.val (.word (524288 : BitVec 64))))
    (watched targets : Set (BitVec 64)) (watchedSubset : watched ⊆ tables)
    (tableValues : ∀ table ∈ watched, HashTableValuesIn table targets state)
    (savedValues : JournalSavedValuesIn journal count.toNat watched targets state)
    (newRegistered : table ∈ watched → value ∈ targets)
    (returnedValue : ValueHOL 64)
    (success : (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jset)).1 = some (.returned returnedValue)) :
    JournalSavedValuesIn journal (count + 1).toNat watched targets (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jset)).2 ∧
    (∀ other ∈ watched, HashTableValuesIn other targets (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_jset)).2) := by
  let bound := setVarHOLFinite (ofString "snap") (.val (.word snapshot)) state
  have locals : ∀ name, name ≠ ofString "snap" → bound.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [bound,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have apart : RollbackPhysicalSeparated widths tables bound := separated.after_read rfl rfl rfl rfl rfl
  obtain ⟨resultSame,frame⟩ := evaluate_fresh_local_nonlocal_state state (ofString "snap") (.val (.word snapshot))
    (sourceFunctionBody Guest.guestFn_jset) jset_snapshot_fresh
  have shadowSuccess : (evaluateHOLFiniteState bound (sourceFunctionBody Guest.guestFn_jset)).1 = some (.returned returnedValue) := resultSame.trans success
  have valid := world.jset_body_registered_values_in apart table key value member supported
    ((locals (ofString "t") (by decide)).trans tableLocal) ((locals (ofString "key") (by decide)).trans keyLocal)
    ((locals (ofString "value") (by decide)).trans valueLocal) keyAligned keyWords keyBytes ticks
    journalBound journalAligned journalHeaders heapDomain capacityGlobal watched targets watchedSubset (by intro other belongs; exact (tableValues other belongs).after_read rfl rfl rfl)
      (savedValues.after_frame (Nat.le_refl _) (by intro index inside offset belongs; rfl)) newRegistered returnedValue shadowSuccess
  have memory := congrArg (fun s : PanSemStateFiniteExact 64 F => s.memory) frame.symm
  have globals := congrArg (fun s : PanSemStateFiniteExact 64 F => s.globals) frame.symm
  have code := congrArg (fun s : PanSemStateFiniteExact 64 F => s.code) frame.symm
  have domain := congrArg (fun s : PanSemStateFiniteExact 64 F => s.memaddrs) frame.symm
  have endian := congrArg (fun s : PanSemStateFiniteExact 64 F => s.be) frame.symm
  exact ⟨valid.1.after_frame (Nat.le_refl _) (by intro index inside offset belongs; exact congrFun memory _),
    (fun other belongs => (valid.2 other belongs).after_read memory domain endian)⟩

#print axioms jset_body_registered_values_in_logical_snapshot
end InitECandidate.Runtime
