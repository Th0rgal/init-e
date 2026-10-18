import InitECandidate.Runtime.VersionedHashesSourceStepBound
import InitECandidate.Runtime.TransactionCostMonotone
import InitECandidate.Runtime.TransactionHeapBudget
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_versioned_hashes_uniform_source_step_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (array index wholeInput wholeLength vh cursor : BitVec 64)
    (arrayLocal : state.locals.lookup (ofString "txs") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (vhLocal : state.locals.lookup (ofString "vh") = some (.val (.word vh)))
    (cursorLocal : state.locals.lookup (ofString "k") = some (.val (.word cursor)))
    (input inputLength scratch frame tx : BitVec 64) (ceiling inputLimit : Nat)
    (slice : RlpSliceInputEntry state array index input inputLength wholeInput wholeLength)
    (wholeBound : wholeLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word tx)))
    (txBound : tx.toNat + 400 ≤ 33806089496) (countLimit : inputLimit * 120 < 2^64)
    (heapArena : ∀ address : BitVec 64, tx.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeFrame : wholeInput.toNat + wholeLength.toNat ≤ frame.toNat)
    (inputBeforeArray : wholeInput.toNat + wholeLength.toNat ≤ tx.toNat)
    (reserve : tx.toNat + transactionHeapWorkspace wholeLength.toNat ≤ frame.toNat)
    (txAligned : tx.toNat % 8 = 0)
    (budget : transactionWrapperCallCost wholeLength.toNat + (1 + versionedHashesScanCost) ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state versionedHashesStep
    state.clock ≤ evaluated.2.clock + (transactionWrapperCallCost wholeLength.toNat + (1 + versionedHashesScanCost)) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have lengthBound := slice.length_bound state array index input inputLength wholeInput wholeLength
  have cost := transaction_wrapper_call_cost_mono inputLength.toNat wholeLength.toNat lengthBound
  have workspace := transaction_heap_workspace_mono inputLength.toNat wholeLength.toNat lengthBound
  have nestedReserve : tx.toNat + transactionHeapWorkspace inputLength.toNat ≤ frame.toNat := by omega
  rw [transaction_heap_workspace_exact] at nestedReserve
  have bounded := evaluate_versioned_hashes_source_step_bounded state array index wholeInput wholeLength vh cursor
    arrayLocal indexLocal vhLocal cursorLocal input inputLength scratch frame tx ceiling inputLimit slice wholeBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap txBound countLimit heapArena
    inputBeforeFrame inputBeforeArray (by simpa only [Nat.add_assoc] using nestedReserve) txAligned (by omega)
  exact ⟨bounded.1.trans (Nat.add_le_add_left (Nat.add_le_add_right cost _) _),bounded.2⟩

#print axioms evaluate_versioned_hashes_uniform_source_step_bounded
end InitECandidate.Runtime
