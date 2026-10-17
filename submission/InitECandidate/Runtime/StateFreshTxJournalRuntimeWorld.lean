import InitECandidate.Runtime.JournalRuntimeWorld
import InitECandidate.Runtime.StateFreshTxJournalReservedFrame
set_option maxRecDepth 10000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual fresh-transaction initialization establishes the full invariant
consumed and preserved by repeated bounded journal mutation calls. -/
theorem evaluate_stateFreshTx_journal_runtime_world {F : Type} (state : PanSemStateFiniteExact 64 F)
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
      (∀ address, address.toNat < (allocationEnd pointer 72).toNat → widths address = base address) := by
  obtain ⟨widths,post,run,world,apart,cost,remaining,domainEq,locals,preserve,headers,journalBound,postCode,_,capacity⟩ :=
    evaluate_stateFreshTx_call_journal_reserved_frame state base pointer oldTs bs journal snapshot oldCount code heap tsGlobal bsGlobal
      journalGlobal counterGlobal reservation journalBefore domain ticks
  refine ⟨widths,post,run,⟨world,apart,journalBound,journalAligned,headers,?_,capacity.trans capacityGlobal,postCode.trans code⟩,
    cost,remaining,locals,preserve⟩
  intro address upper
  rw [domainEq]
  exact domain address upper

#print axioms evaluate_stateFreshTx_journal_runtime_world
end InitECandidate.Runtime
