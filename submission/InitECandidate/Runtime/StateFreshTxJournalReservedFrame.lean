import InitECandidate.Runtime.StateFreshTxCallReadyFrame
import InitECandidate.Runtime.StateFreshTxRegistryLowerBound
set_option maxRecDepth 10000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Fresh-transaction initialization retains the full journal-buffer separation
needed by every later append, not only the currently empty live prefix. -/
theorem evaluate_stateFreshTx_call_journal_reserved_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (base : BitVec 64 → BitVec 64) (pointer oldTs bs journal snapshot oldCount : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (tsGlobal : state.globals.lookup (ofString "ts") = some (.val (.word oldTs)))
    (bsGlobal : state.globals.lookup (ofString "bs") = some (.val (.word bs)))
    (journalGlobal : state.globals.lookup (ofString "journal") = some (.val (.word journal)))
    (counterGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word oldCount)))
    (reservation : pointer.toNat + 23024 ≤ 33806089496)
    (journalBefore : journal.toNat + 524288 * 32 ≤ pointer.toNat)
    (domain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (ticks : 338 ≤ state.clock) :
    ∃ widths post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "state_fresh_tx") []) = (none,post) ∧
      RollbackWorld widths (stateFreshTxRegistryAfter (allocationEnd pointer 72) stateFreshTxAllTables ∅) journal snapshot 0
        (setVarHOLFinite (ofString "snap") (.val (.word snapshot)) post) ∧
      RollbackPhysicalSeparated widths (stateFreshTxRegistryAfter (allocationEnd pointer 72) stateFreshTxAllTables ∅) post ∧
      state.clock ≤ post.clock + 338 ∧ post.clock ≤ state.clock ∧ post.memaddrs = state.memaddrs ∧ post.locals = state.locals ∧
      (∀ address, address.toNat < (allocationEnd pointer 72).toNat → widths address = base address) ∧
      (∀ table ∈ stateFreshTxRegistryAfter (allocationEnd pointer 72) stateFreshTxAllTables ∅,
        journal.toNat + 524288 * 32 ≤ table.toNat) ∧ journal.toNat + 524288 * 32 ≤ 33806089496 ∧ post.code = state.code ∧ post.be = state.be ∧
      post.globals.lookup (ofString "journal_cap") = state.globals.lookup (ofString "journal_cap") := by
  obtain ⟨widths,post,run,world,apart,cost,remaining,domainEq,locals,preserve,postCode,postEndian,postGlobals⟩ :=
    evaluate_stateFreshTx_call_ready_frame state base pointer oldTs bs journal snapshot oldCount code heap tsGlobal bsGlobal journalGlobal counterGlobal
      reservation (by omega) domain ticks
  obtain ⟨_,headerSpace,space⟩ := stateFreshTx_reservation pointer reservation
  have covers := allocationEnd_covers pointer (72 : BitVec 64) headerSpace
  have fullHeaders := stateFreshTx_registry_lower_bound stateFreshTxAllTables (allocationEnd pointer 72) ∅
    (journal.toNat + 524288 * 32) stateFreshTx_all_literals (by omega)
    (by intro table member; exact False.elim member) (by simpa only [stateFreshTx_all_budgets.1] using space)
  exact ⟨widths,post,run,world,apart,cost,remaining,domainEq,locals,preserve,fullHeaders,by omega,postCode,postEndian,postGlobals (ofString "journal_cap") (by decide) (by decide) (by decide)⟩

#print axioms evaluate_stateFreshTx_call_journal_reserved_frame
end InitECandidate.Runtime
