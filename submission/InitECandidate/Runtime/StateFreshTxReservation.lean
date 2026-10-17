import InitECandidate.Runtime.StateFreshTxBodyReady
set_option maxRecDepth 10000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A single natural reservation proves the allocator guard and room for all
transaction tables, including at most seven header-alignment padding bytes. -/
theorem stateFreshTx_reservation (pointer : BitVec 64)
    (reservation : pointer.toNat + 23024 ≤ 33806089496) :
    (72 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer ∧
      pointer.toNat + 72 ≤ 33806089496 ∧
      (allocationEnd pointer 72).toNat + 22944 ≤ 33806089496 := by
  have pointerLe : pointer ≤ (33806089496 : BitVec 64) := BitVec.le_def.mpr (by change pointer.toNat ≤ 33806089496; omega)
  have gap : ((33806089496 : BitVec 64) - pointer).toNat = 33806089496 - pointer.toNat := by
    rw [BitVec.toNat_sub_of_le pointerLe]; rfl
  have headerSpace : pointer.toNat + (72 : BitVec 64).toNat ≤ 33806089496 := by change pointer.toNat + 72 ≤ _; omega
  have covers := allocationEnd_covers pointer (72 : BitVec 64) headerSpace
  refine ⟨BitVec.le_def.mpr ?_,headerSpace,?_⟩
  · rw [gap]; change 72 ≤ _; omega
  · have upper : (allocationEnd pointer 72).toNat < pointer.toNat + 72 + 8 := covers.2.1
    omega

/-- Full source body with the allocator premises reduced to one reservation. -/
theorem evaluate_stateFreshTx_body_reserved {F : Type} (state : PanSemStateFiniteExact 64 F)
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
      (∀ address, address.toNat < (allocationEnd pointer 72).toNat → widths address = base address) := by
  obtain ⟨request,headerSpace,budget⟩ := stateFreshTx_reservation pointer reservation
  exact evaluate_stateFreshTx_body_ready state base pointer oldTs bs journal snapshot oldCount code heap tsGlobal bsGlobal
    journalGlobal counterGlobal request headerSpace budget journalBefore domain ticks

#print axioms stateFreshTx_reservation
#print axioms evaluate_stateFreshTx_body_reserved
end InitECandidate.Runtime
