import InitECandidate.Runtime.StateRestoreRecordApplicationNoTimeout
import InitECandidate.Runtime.HashTableReadyGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original decrement plus record application has the same clock bound. -/
theorem HashTableReady.restore_iteration_no_timeout {F : Type} (state : PanSemStateFiniteExact 64 F)
    (keyLength table pointer keys stride capacity used values order orderPos items key journal count present value : BitVec 64) (bits : Nat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (ready : HashTableReady keyLength table keys stride capacity used values order orderPos items bits pointer state)
    (strideBound : stride.toNat ≤ 56) (capacityLarge : 1 < capacity.toNat)
    (ticks : 2 ^ 72 ≤ state.clock)
    (domain : ∀ address : BitVec 64, table.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (journalGlobal : state.globals.lookup (ofString "journal") = some (.val (.word journal)))
    (countGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word count)))
    (tableDomain : state.memaddrs (journal + (count - 1) * 32))
    (tableCell : state.memory (journal + (count - 1) * 32) = .word table)
    (keyDomain : state.memaddrs (journal + (count - 1) * 32 + 8))
    (keyCell : state.memory (journal + (count - 1) * 32 + 8) = .word key)
    (presentDomain : state.memaddrs (journal + (count - 1) * 32 + 16)) (presentCell : state.memory (journal + (count - 1) * 32 + 16) = .word present)
    (valueDomain : state.memaddrs (journal + (count - 1) * 32 + 24)) (valueCell : state.memory (journal + (count - 1) * 32 + 24) = .word value)
    (keyAligned : key.toNat % 8 = 0)
    (keyWords : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (key + BitVec.ofNat 64 offset))
    (keyBytes : ∀ offset : Nat, offset < keyLength.toNat → state.memaddrs (panByteAlignHOL (key + BitVec.ofNat 64 offset))) :
    (evaluateHOLFiniteState state stateRestoreLoopBody).1 ≠ some .timeOut ∧
    state.clock ≤ (evaluateHOLFiniteState state stateRestoreLoopBody).2.clock + 2 ^ 72 ∧
      (evaluateHOLFiniteState state stateRestoreLoopBody).2.clock ≤ state.clock := by
  let entry := setGlobalHOLFinite (ofString "journal_n") (.val (.word (count - 1))) state
  have entryReady := ready.after_global state keyLength table pointer keys stride capacity used values order orderPos items bits
    (ofString "journal_n") (.val (.word (count - 1))) (by decide)
  have journalAfter : entry.globals.lookup (ofString "journal") = some (.val (.word journal)) := by
    have distinct : ofString "journal_n" ≠ ofString "journal" := by decide
    simpa [entry,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,distinct] using journalGlobal
  have countAfter : entry.globals.lookup (ofString "journal_n") = some (.val (.word (count - 1))) := by
    simp [entry,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have bounded := entryReady.restore_record_application_no_timeout entry keyLength table pointer keys stride capacity used values order orderPos items key journal (count - 1) present value bits supported strideBound capacityLarge ticks domain
    journalAfter countAfter tableDomain tableCell keyDomain keyCell presentDomain presentCell valueDomain valueCell keyAligned keyWords keyBytes
  have run := evaluate_seq_none (evaluate_stateRestore_decrement state count countGlobal)
    (show evaluateHOLFiniteState (setKvarHOLFinite .global (ofString "journal_n") (.val (.word (count - 1))) state) stateRestoreApplyRecord = evaluateHOLFiniteState entry stateRestoreApplyRecord from rfl)
  rw [stateRestore_loop_body_shape,run]
  exact bounded

#print axioms HashTableReady.restore_iteration_no_timeout
end InitECandidate.Runtime
