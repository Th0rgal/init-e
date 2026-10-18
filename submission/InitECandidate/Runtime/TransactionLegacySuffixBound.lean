import InitECandidate.Runtime.TransactionLegacyReturnedContinuationBound
import InitECandidate.Runtime.TransactionTypedSuffixBound
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_legacy_suffix_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (input inputLength scratch frame array tx : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word input)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word inputLength)))
    (noWrap : input.toNat + inputLength.toNat < 2^64)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 120 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ input.toNat))
    (inputBeforeArray : input.toNat + inputLength.toNat ≤ array.toNat)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (typeLocal : state.locals.lookup (ofString "t") = some (.val (.word (0 : BitVec 64))))
    (countLocal : state.locals.lookup (ofString "nfields") = some (.val (.word (9 : BitVec 64))))
    (headerBefore : tx.toNat + 344 < array.toNat)
    (reserve : array.toNat + inputLength.toNat * 56 + (inputLength.toNat * 48 + 46) * inputLength.toNat + inputLength.toNat * 296 + 14 ≤ frame.toNat)
    (budget : transactionTypedSuffixCost inputLength.toNat inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.seq transactionLegacyPath (transactionAt 10))
    state.clock ≤ evaluated.2.clock + transactionTypedSuffixCost inputLength.toNat inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let first := inputLength.toNat * ((2 * inputLength.toNat + 1) * 15 + 19) + 92635
  let tail := transactionListSuffixCost inputLength.toNat inputLength.toNat
  have ticks : first + tail ≤ state.clock := budget
  have firstBudget : first ≤ state.clock := by omega
  have args := transaction_legacy_decode_arguments state input inputLength pointerLocal lengthLocal
  have bounded := evaluate_rlpDecodeFully_call_bounded state (some (.local,ofString "top")) transactionLegacyDecodeArguments
    input inputLength scratch frame ceiling inputLimit args (by omega) (by omega) limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena firstBudget
  rw [source_transaction_legacy_decode,evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState state
      (.call (some (some (.local,ofString "top"),none)) (ofString "rlp_decode_fully") transactionLegacyDecodeArguments) with
  | mk result post =>
    rw [run] at bounded
    dsimp only at bounded ⊢
    cases result with
    | some result =>
      exact ⟨by change state.clock ≤ post.clock + (first + tail); have spent := bounded.1; omega,bounded.2⟩
    | none =>
      dsimp only
      have futureTicks : tail ≤ post.clock := by have spent := bounded.1; omega
      have remaining := transaction_legacy_returned_continuation_bounded state post input inputLength scratch frame array tx ceiling inputLimit
        pointerLocal lengthLocal noWrap inputBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap
        arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray txLocal typeLocal countLocal headerBefore reserve
        (by dsimp [first] at firstBudget; omega) futureTicks run
      exact ⟨by change state.clock ≤ _ + (first + tail); have spent := bounded.1; have rest := remaining.1; omega,
        Nat.le_trans remaining.2.1 bounded.2.1,remaining.2.2⟩

#print axioms transaction_legacy_suffix_bounded
end InitECandidate.Runtime
