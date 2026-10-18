import InitECandidate.Runtime.VersionedHashesSourceStepBound
import InitECandidate.Runtime.VersionedHashesTransactionStepOuterPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem versioned_hashes_source_step_normal_outer_prefix {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (inputBeforeFrame : wholeInput.toNat + wholeLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ wholeInput.toNat))
    (inputBeforeArray : wholeInput.toNat + wholeLength.toNat ≤ tx.toNat)
    (reserve : tx.toNat + 400 + inputLength.toNat * 56 + (inputLength.toNat * 48 + 46) * inputLength.toNat + inputLength.toNat * 296 + 14 ≤ frame.toNat)
    (txAligned : tx.toNat % 8 = 0)
    (budget : transactionWrapperCallCost inputLength.toNat ≤ state.clock)
    (heapSpace : tx.toNat + 400 + inputLength.toNat * 16 ≤ 33806089496)
    (outerArray outerCount outerInput outerLength : BitVec 64)
    (outerValid : RlpSliceInputPrefix state outerArray outerInput outerLength outerCount.toNat)
    (outerBelow : outerArray.toNat + outerCount.toNat * 16 ≤ frame.toNat)
    (beforeTx : outerArray.toNat + outerCount.toNat * 16 ≤ tx.toNat)
    (run : evaluateHOLFiniteState state versionedHashesStep = (none,post)) :
    RlpSliceInputPrefix post outerArray outerInput outerLength outerCount.toNat := by
  have args := transaction_slice_arguments state (ofString "txs") (ofString "i") array index input inputLength
    arrayLocal indexLocal slice.readable
  have lengthBound := slice.length_bound state array index input inputLength wholeInput wholeLength
  rw [source_versioned_hashes_step] at run
  exact versioned_hashes_transaction_step_normal_outer_prefix state post
    (transactionSliceArguments (ofString "txs") (ofString "i")) vh cursor vhLocal cursorLocal
    input inputLength scratch frame tx ceiling inputLimit args slice.noWrap (by omega) limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap txBound countLimit heapArena
    (by have span := slice.endsWithin; have start := slice.startsWithin; omega) (by have span := slice.endsWithin; have start := slice.startsWithin; omega) reserve txAligned budget
    heapSpace outerArray outerCount outerInput outerLength outerValid outerBelow beforeTx run

#print axioms versioned_hashes_source_step_normal_outer_prefix
end InitECandidate.Runtime
