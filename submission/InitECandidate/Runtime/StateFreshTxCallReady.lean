import InitECandidate.Runtime.StateFreshTxReservation
import InitECandidate.Runtime.OriginalStateFreshTxCode
import InitECandidate.Runtime.PanNoArgsLookup
set_option maxRecDepth 10000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An actual no-argument fresh-transaction call initializes the separated
rollback world, restores caller locals and consumes at most 338 source clocks. -/
theorem evaluate_stateFreshTx_call_ready {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (ticks : 338 ≤ state.clock) :
    ∃ widths post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "state_fresh_tx") []) = (none,post) ∧
      RollbackWorld widths (stateFreshTxRegistryAfter (allocationEnd pointer 72) stateFreshTxAllTables ∅) journal snapshot 0
        (setVarHOLFinite (ofString "snap") (.val (.word snapshot)) post) ∧
      RollbackPhysicalSeparated widths (stateFreshTxRegistryAfter (allocationEnd pointer 72) stateFreshTxAllTables ∅) post ∧
      state.clock ≤ post.clock + 338 ∧ post.clock ≤ state.clock ∧ post.memaddrs = state.memaddrs ∧ post.locals = state.locals ∧
      (∀ address, address.toNat < (allocationEnd pointer 72).toNat → widths address = base address) := by
  let entry := callEntryStateHOLFinite state HolFiniteMapExact.empty
  obtain ⟨widths,bodyPost,body,world,apart,cost,remaining,addresses,preserve⟩ :=
    evaluate_stateFreshTx_body_reserved entry base pointer oldTs bs journal snapshot oldCount code heap tsGlobal bsGlobal
      journalGlobal counterGlobal reservation journalBefore domain (by change 337 ≤ state.clock - 1; omega)
  let exited := {emptyLocalsHOLFinite bodyPost with locals := HolFiniteMapExact.resVarEq (emptyLocalsHOLFinite bodyPost).locals (ofString "t",entry.locals.lookup (ofString "t"))}
  let post := {bodyPost with locals := state.locals}
  have installed : state.code.lookup (ofString "state_fresh_tx") = some ([],sourceFunctionBody Guest.guestFn_state_fresh_tx,.one) := by
    rw [code]; exact originalRuntimeCode_stateFreshTx_lookup
  have lookup := pan_no_args_lookup state.code.lookup (ofString "state_fresh_tx") (sourceFunctionBody Guest.guestFn_state_fresh_tx) installed
  have call := evaluateHOLFiniteState_call_return_caller_locals state none (ofString "state_fresh_tx") [] []
    (sourceFunctionBody Guest.guestFn_state_fresh_tx) HolFiniteMapExact.empty .one (.val (.word (0 : BitVec 64))) exited
    rfl lookup (by omega) body (by simp [shapeOfHOLExact,shapeEqHOL])
  have worldPost : RollbackWorld widths (stateFreshTxRegistryAfter (allocationEnd pointer 72) stateFreshTxAllTables ∅) journal snapshot 0
      (setVarHOLFinite (ofString "snap") (.val (.word snapshot)) post) :=
    world.after_read rfl rfl rfl rfl rfl (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
  have entryClock : entry.clock = state.clock - 1 := rfl
  refine ⟨widths,post,call,worldPost,apart.after_read rfl rfl rfl rfl rfl,by change state.clock ≤ bodyPost.clock + 338; omega,
    by change bodyPost.clock ≤ state.clock; omega,addresses,rfl,preserve⟩

#print axioms evaluate_stateFreshTx_call_ready
end InitECandidate.Runtime
