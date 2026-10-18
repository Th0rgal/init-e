import InitECandidate.Runtime.VersionedHashesTransactionStepBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_versioned_hashes_source_step_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
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
    (reserve : tx.toNat + 400 + inputLength.toNat * 56 + (inputLength.toNat * 48 + 46) * inputLength.toNat + inputLength.toNat * 296 + 14 ≤ frame.toNat)
    (txAligned : tx.toNat % 8 = 0)
    (budget : transactionWrapperCallCost inputLength.toNat + (1 + versionedHashesScanCost) ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state versionedHashesStep
    state.clock ≤ evaluated.2.clock + (transactionWrapperCallCost inputLength.toNat + (1 + versionedHashesScanCost)) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have args := transaction_slice_arguments state (ofString "txs") (ofString "i") array index input inputLength
    arrayLocal indexLocal slice.readable
  have lengthBound := slice.length_bound state array index input inputLength wholeInput wholeLength
  rw [source_versioned_hashes_step]
  exact evaluate_versioned_hashes_transaction_step_bounded state
    (transactionSliceArguments (ofString "txs") (ofString "i")) vh cursor vhLocal cursorLocal
    input inputLength scratch frame tx ceiling inputLimit args slice.noWrap (by omega) limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap txBound countLimit heapArena
    (by have span := slice.endsWithin; omega) (by have span := slice.endsWithin; omega) reserve txAligned budget

/-- Failed original pointer/length argument loads reject before entering the
transaction decoder, without consuming a source clock tick. -/
theorem evaluate_versioned_hashes_source_step_missing_arguments {F : Type} (state : PanSemStateFiniteExact 64 F)
    (missing : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      (transactionSliceArguments (ofString "txs") (ofString "i")) = none) :
    evaluateHOLFiniteState state versionedHashesStep = (some .error,state) := by
  rw [source_versioned_hashes_step]
  exact evaluateHOLFiniteState_decCall_args_none state (ofString "tx") .one (ofString "decode_transaction")
    (transactionSliceArguments (ofString "txs") (ofString "i")) _ missing

#print axioms evaluate_versioned_hashes_source_step_missing_arguments
#print axioms evaluate_versioned_hashes_source_step_bounded
end InitECandidate.Runtime
