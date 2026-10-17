import InitECandidate.Runtime.StateFreshTxAllocate
import InitECandidate.Runtime.StateFreshTxTablesReady
set_option maxRecDepth 10000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Full original fresh-transaction body, including header allocation, all eight
tables and journal reset, establishes the empty separated rollback world. -/
theorem evaluate_stateFreshTx_body_ready {F : Type} (state : PanSemStateFiniteExact 64 F)
    (base : BitVec 64 → BitVec 64) (pointer oldTs bs journal snapshot oldCount : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (tsGlobal : state.globals.lookup (ofString "ts") = some (.val (.word oldTs)))
    (bsGlobal : state.globals.lookup (ofString "bs") = some (.val (.word bs)))
    (journalGlobal : state.globals.lookup (ofString "journal") = some (.val (.word journal)))
    (counterGlobal : state.globals.lookup (ofString "journal_n") = some (.val (.word oldCount)))
    (request : (72 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (headerSpace : pointer.toNat + 72 ≤ 33806089496)
    (budget : (allocationEnd pointer 72).toNat + 22944 ≤ 33806089496)
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
  obtain ⟨middle,allocationRun,clock,locals,midCode,addresses,_,_,ts,heapNext,globals⟩ :=
    evaluate_stateFreshTx_allocate state pointer oldTs bs code (by omega) heap tsGlobal bsGlobal request (by omega) (domain pointer (by omega))
  have covers := allocationEnd_covers pointer (72 : BitVec 64) headerSpace
  obtain ⟨widths,post,finish,world,apart,cost,remaining,postDomain,preserve⟩ :=
    evaluate_stateFreshTx_tables_ready middle base (allocationEnd pointer 72) pointer journal snapshot oldCount
      (midCode.trans code) heapNext ts ((globals (ofString "journal") (by decide) (by decide)).trans journalGlobal)
      ((globals (ofString "journal_n") (by decide) (by decide)).trans counterGlobal)
      covers.2.2 covers.1 journalBefore (by intro address bound; rw [addresses]; exact domain address bound) budget (by omega)
  refine ⟨widths,post,?_,world,apart,by omega,by omega,postDomain.trans addresses,preserve⟩
  rw [source_stateFreshTx_body,← evaluate_seq_assoc]
  rw [evaluateHOLFiniteState_seq_line780,allocationRun]
  simpa only [locals] using finish

#print axioms evaluate_stateFreshTx_body_ready
end InitECandidate.Runtime
