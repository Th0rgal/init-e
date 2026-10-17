import InitECandidate.Runtime.JournalRuntimeWorld
import InitECandidate.Runtime.StateFreshTxJournalRuntimeWorld
import InitECandidate.Runtime.StateFreshTxCallReadyFields
set_option maxRecDepth 10000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual fresh-transaction initialization establishes the full invariant
consumed and preserved by repeated bounded journal mutation calls. -/
theorem evaluate_stateFreshTx_journal_runtime_world_fields {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (ticks : 338 ≤ state.clock)
    (journalAligned : journal.toNat % 8 = 0)
    (capacityGlobal : state.globals.lookup (ofString "journal_cap") = some (.val (.word (524288 : BitVec 64)))) :
    ∃ widths post, evaluateHOLFiniteState state (.call (some (none,none)) (ofString "state_fresh_tx") []) = (none,post) ∧
      JournalRuntimeWorld widths (stateFreshTxRegistryAfter (allocationEnd pointer 72) stateFreshTxAllTables ∅) journal snapshot 0 post ∧
      state.clock ≤ post.clock + 338 ∧ post.clock ≤ state.clock ∧ post.locals = state.locals ∧
      (∀ address, address.toNat < (allocationEnd pointer 72).toNat → widths address = base address) ∧
      StateFreshTxFields pointer (allocationEnd pointer 72) stateFreshTxAllTables post ∧
      post.globals.lookup (ofString "ts") = some (.val (.word pointer)) := by
  obtain ⟨widths,post,run,world,cost,remaining,locals,preserve⟩ :=
    evaluate_stateFreshTx_journal_runtime_world state base pointer oldTs bs journal snapshot oldCount code heap tsGlobal bsGlobal
      journalGlobal counterGlobal reservation journalBefore domain ticks journalAligned capacityGlobal
  obtain ⟨_,checked,checkedRun,_,_,_,_,_,_,_,_,_,_,_,fields,tsAfter⟩ :=
    evaluate_stateFreshTx_call_ready_fields state base pointer oldTs bs journal snapshot oldCount code heap tsGlobal bsGlobal
      journalGlobal counterGlobal reservation (by omega) domain ticks
  have same : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  rw [← same] at fields tsAfter
  exact ⟨widths,post,run,world,cost,remaining,locals,preserve,fields,tsAfter⟩

#print axioms evaluate_stateFreshTx_journal_runtime_world_fields
end InitECandidate.Runtime
