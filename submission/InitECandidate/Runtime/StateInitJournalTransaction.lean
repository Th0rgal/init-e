import InitECandidate.Runtime.StateInitJournalAllocate
import InitECandidate.Runtime.StateFreshTxTransactionRuntimeWorld
import InitECandidate.Runtime.AllocationBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual journal-initialization suffix followed by a fresh-transaction
call establishes the recurrent invariant within339 source clocks. The preceding
witness decoding and block-table constructors are outside this suffix contract. -/
theorem evaluate_stateInit_journal_then_transaction {F : Type} (state : PanSemStateFiniteExact 64 F)
    (base : BitVec 64 → BitVec 64) (pointer oldCapacity oldJournal oldCount oldTs bs snapshot : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (capacity : state.globals.lookup (ofString "journal_cap") = some (.val (.word oldCapacity)))
    (journal : state.globals.lookup (ofString "journal") = some (.val (.word oldJournal)))
    (counter : state.globals.lookup (ofString "journal_n") = some (.val (.word oldCount)))
    (ts : state.globals.lookup (ofString "ts") = some (.val (.word oldTs)))
    (blockState : state.globals.lookup (ofString "bs") = some (.val (.word bs)))
    (aligned : pointer.toNat % 8 = 0)
    (reservation : pointer.toNat + 16777216 + 23032 ≤ 33806089496)
    (domain : ∀ address : BitVec 64, address.toNat < 33806089496 → state.memaddrs address)
    (ticks : 339 ≤ state.clock) :
    ∃ widths initialized post,
      evaluateHOLFiniteState state stateInitJournalTail = (some (.returned (.val (.word (0 : BitVec 64)))),initialized) ∧
      evaluateHOLFiniteState initialized (.call (some (none,none)) (ofString "state_fresh_tx") []) = (none,post) ∧
      TransactionRuntimeWorld widths (allocationEnd (allocationEnd pointer 16777216) 72)
        (allocationEnd pointer 16777216) pointer snapshot 0 post ∧
      state.clock ≤ post.clock + 339 ∧ post.clock ≤ state.clock := by
  have pointerLe : pointer ≤ (33806089496 : BitVec 64) := BitVec.le_def.mpr (by change pointer.toNat ≤ 33806089496; omega)
  have gap : ((33806089496 : BitVec 64) - pointer).toNat = 33806089496 - pointer.toNat := by
    rw [BitVec.toNat_sub_of_le pointerLe]; rfl
  have request : (16777216 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer := by
    apply BitVec.le_def.mpr
    rw [gap]
    change 16777216 ≤ _
    omega
  have finish := allocationEnd_within_heap pointer 16777216 (by omega) request
  have covers := allocationEnd_covers pointer (16777216 : BitVec 64) (by change pointer.toNat + 16777216 ≤ 33806089496; omega)
  obtain ⟨allocated,setup,clock,_,_,postCode,addresses,_,capAfter,journalAfter,counterAfter,tsAfter,heapAfter,globals⟩ :=
    evaluate_stateInit_journal_setup state pointer oldCapacity oldJournal oldCount oldTs code (by omega)
      heap capacity journal counter ts request finish
  let initialized := emptyLocalsHOLFinite allocated
  have initClock : initialized.clock = state.clock - 1 := clock
  have bsAfter : initialized.globals.lookup (ofString "bs") = some (.val (.word bs)) :=
    (globals (ofString "bs") (by decide) (by decide) (by decide) (by decide) (by decide)).trans blockState
  obtain ⟨widths,post,run,world,cost,remaining,_,_⟩ :=
    evaluate_stateFreshTx_transaction_runtime_world initialized base (allocationEnd pointer 16777216) 0 bs pointer snapshot 0
      (postCode.trans code) heapAfter tsAfter bsAfter journalAfter counterAfter
      (by have upper := covers.2.1; change (allocationEnd pointer 16777216).toNat < pointer.toNat + 16777216 + 8 at upper; omega)
      covers.1 (by intro address upper; change allocated.memaddrs address; rw [addresses]; exact domain address upper)
      (by omega) aligned capAfter
  refine ⟨widths,initialized,post,?_,run,world,by omega,by omega⟩
  rw [stateInitJournalTail_eq_setup,setup]
  simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,initialized]

#print axioms evaluate_stateInit_journal_then_transaction
end InitECandidate.Runtime
