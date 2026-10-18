import InitECandidate.Runtime.TransactionListReturnedContinuationBound
import InitECandidate.Runtime.PanDecCallCheckedContinuationBound
import InitECandidate.Runtime.RlpSlicesBodyBound
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def transactionListSuffixCost (length inputLength : Nat) : Nat :=
  (length * ((2 * length + 1) * 15 + 19) + length * 12 + 4) + transactionChainIdSuffixCost inputLength

theorem transaction_list_suffix_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame array input inputLength tx kind expected tag total : BitVec 64) (ceiling inputLimit : Nat)
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 120 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat)
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (starts : input.toNat ≤ pointer.toNat)
    (ends : pointer.toNat + length.toNat ≤ input.toNat + inputLength.toNat)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (typeLocal : state.locals.lookup (ofString "t") = some (.val (.word kind)))
    (wholeInputBeforeArray : input.toNat + inputLength.toNat ≤ array.toNat)
    (expectedLocal : state.locals.lookup (ofString "nfields") = some (.val (.word expected)))
    (fields : transactionRequiredFields kind ≤ expected.toNat)
    (inputBound : inputLength.toNat ≤ inputLimit)
    (headerBefore : tx.toNat + 344 < array.toNat)
    (reserve : array.toNat + inputLength.toNat * 56 + (inputLength.toNat * 48 + 46) * inputLength.toNat + inputLength.toNat * 296 + 14 ≤ frame.toNat)
    (topLocal : state.locals.lookup (ofString "top") = some (.rStruct [.val (.word tag),.val (.word pointer),.val (.word length),.val (.word total)]))
    (budget : transactionListSuffixCost length.toNat inputLength.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (transactionAt 12)
    state.clock ≤ evaluated.2.clock + transactionListSuffixCost length.toNat inputLength.toNat ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let first := length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 4
  let tail := transactionChainIdSuffixCost inputLength.toNat
  have ticks : first + tail ≤ state.clock := budget
  have firstBudget : first ≤ state.clock := by omega
  let callee := transactionListCallee pointer length
  let entry := callEntryStateHOLFinite state callee
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callee,callEntryStateHOLFinite,transactionListCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,callEntryStateHOLFinite,transactionListCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryBudget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + length.toNat * 12 + 3 ≤ entry.clock := by
    change _ ≤ state.clock - 1
    dsimp [first] at firstBudget
    omega
  have bounded := evaluate_rlpSlices_body_bounded entry pointer length scratch frame ceiling inputLimit atPointer atLength noWrap lengthBound limitBound
    scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena entryBudget
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) with
  | mk result post =>
    rw [bodyRun] at bounded
    dsimp only at bounded
    rw [source_transaction_list]
    apply evaluate_decCall_checked_continuation_bounded state post (ofString "lst") (ofString "rlp_list_to_slices")
      (.comb [.one,.one]) (.comb [.one,.one]) transactionListArguments _ _ (transactionAt 13) callee result first tail
      (transaction_list_arguments state tag pointer length total topLocal) (transaction_list_lookup state pointer length code)
      (by dsimp [first] at firstBudget; omega) bodyRun bounded.2.1
      (by have spent := bounded.1; change state.clock - 1 ≤ post.clock + _ at spent; dsimp [first]; omega) bounded.2.2
    intro value returned checked
    have actualBody : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_rlp_list_to_slices) = (some (.returned value),post) := by
      rw [bodyRun,returned]
    have futureBudget : tail ≤ post.clock := by
      have spent := bounded.1
      change state.clock - 1 ≤ post.clock + _ at spent
      dsimp [first] at ticks
      omega
    exact transaction_list_returned_continuation_bounded state post pointer length scratch frame array input inputLength tx kind expected ceiling inputLimit
      noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena
      firstBudget inputBeforeFrame inputBeforeArray starts ends txLocal typeLocal wholeInputBeforeArray expectedLocal fields inputBound headerBefore reserve
      futureBudget value actualBody

#print axioms transaction_list_suffix_bounded
end InitECandidate.Runtime
