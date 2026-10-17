import InitECandidate.Runtime.StateFreshTxBodyReadyFields
import InitECandidate.Runtime.StateFreshTxReservation
set_option maxRecDepth 10000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Full metadata contract with one numeric allocation reservation. -/
theorem evaluate_stateFreshTx_body_reserved_fields {F : Type} (state : PanSemStateFiniteExact 64 F)
    (base : BitVec 64 → BitVec 64) (pointer oldTs bs journal snapshot oldCount : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (tsGlobal : state.globals.lookup (ofString "ts") = some (.val (.word oldTs)))
    (bsGlobal : state.globals.lookup (ofString "bs") = some (.val (.word bs)))
    (journalGlobal : state.globals.lookup (ofString "journal") = some (.val (.word journal)))
    (counterGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word oldCount)))
    (reservation : pointer.toNat + 23024 ≤ 33806089496)
    (journalBefore : journal.toNat ≤ pointer.toNat + 72)
    (domain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (ticks : 337 ≤ state.clock) :
    ∃ widths post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_state_fresh_tx) =
      (some (.returned (.val (.word (0 : BitVec 64)))),
        {emptyLocalsHOLFinite post with locals := HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite post).locals (ofString "t",state.locals.lookup (ofString "t"))}) ∧
      RollbackWorld widths (stateFreshTxRegistryAfter (allocationEnd pointer 72) stateFreshTxAllTables ∅) journal snapshot 0
        (setVarHOLFinite (ofString "snap") (.val (.word snapshot)) post) ∧
      RollbackPhysicalSeparated widths (stateFreshTxRegistryAfter (allocationEnd pointer 72) stateFreshTxAllTables ∅) post ∧
      state.clock ≤ post.clock + 337 ∧ post.clock ≤ state.clock ∧ post.memaddrs = state.memaddrs ∧
      (∀ address, address.toNat < (allocationEnd pointer 72).toNat → widths address = base address) ∧ post.code = state.code ∧ post.be = state.be ∧
      (∀ name, name ≠ ofString "heap_ptr" → name ≠ ofString "journal_n" → name ≠ ofString "ts" → post.globals.lookup name = state.globals.lookup name) ∧
      (∀ table ∈ stateFreshTxRegistryAfter (allocationEnd pointer 72) stateFreshTxAllTables ∅, widths table = 20 ∨ widths table = 32 ∨ widths table = 52) ∧
      StateFreshTxFields pointer (allocationEnd pointer 72) stateFreshTxAllTables post ∧
      post.globals.lookup (ofString "ts") = some (.val (.word pointer)) := by
  obtain ⟨request,headerSpace,budget⟩ := stateFreshTx_reservation pointer reservation
  exact evaluate_stateFreshTx_body_ready_fields state base pointer oldTs bs journal snapshot oldCount code heap tsGlobal bsGlobal
    journalGlobal counterGlobal request headerSpace budget journalBefore domain ticks

#print axioms evaluate_stateFreshTx_body_reserved_fields
end InitECandidate.Runtime
