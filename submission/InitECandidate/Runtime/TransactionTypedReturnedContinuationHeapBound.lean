import InitECandidate.Runtime.TransactionTypeAssignSuffixHeapBound
import InitECandidate.Runtime.TransactionTypedDecodeSource
import InitECandidate.Runtime.RlpDecodeFullyLocalCallRuntimeContract
import InitECandidate.Runtime.TransactionListCostMonotone
import InitECandidate.Runtime.NormalLocalFrame
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_typed_returned_continuation_heap_bounded {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (input inputLength scratch frame array tx kind oldKind : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word input)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word inputLength)))
    (positive : 0 < inputLength.toNat) (noWrap : input.toNat + inputLength.toNat < 2^64)
    (inputBound : inputLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 120 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → state.memaddrs address)
    (inputBeforeFrame : input.toNat + inputLength.toNat ≤ frame.toNat)
    (inputBeforeArray : input.toNat + inputLength.toNat ≤ array.toNat)
    (txLocal : state.locals.lookup (ofString "tx") = some (.val (.word tx)))
    (typeLocal : state.locals.lookup (ofString "t") = some (.val (.word oldKind)))
    (byteLocal : state.locals.lookup (ofString "b0") = some (.val (.word kind)))
    (countLocal : state.locals.lookup (ofString "nfields") = some (.val (.word (9 : BitVec 64))))
    (supported : kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 ∨ kind = 4)
    (headerBefore : tx.toNat + 344 < array.toNat)
    (arrayAbove : ceiling ≤ array.toNat)
    (budget : (inputLength - 1).toNat * ((2 * (inputLength - 1).toNat + 1) * 15 + 19) + 92634 ≤ state.clock)
    (futureBudget : transactionListSuffixCost inputLength.toNat inputLength.toNat ≤ post.clock)
    (run : evaluateHOLFiniteState state (.call (some (some (.local,ofString "top"),none)) (ofString "rlp_decode_fully") transactionTypedDecodeArguments) = (none,post)) :
    let evaluated := evaluateHOLFiniteState post (.seq transactionTypeAssign (.seq transactionTypeFields (transactionAt 10)))
    post.clock ≤ evaluated.2.clock + transactionListSuffixCost inputLength.toNat inputLength.toNat ∧
      evaluated.2.clock ≤ post.clock ∧ evaluated.1 ≠ some .timeOut := by
  have range := transaction_typed_decode_range input inputLength positive noWrap
  have args := transaction_typed_decode_arguments state input inputLength pointerLocal lengthLocal
  obtain ⟨tag,pointer,length,topLocal,flag,payloadBound,_,ends,payloadNoWrap,starts,globals⟩ :=
    rlpDecodeFully_local_call_runtime_contract state post (ofString "top") transactionTypedDecodeArguments
      (input + 1) (inputLength - 1) scratch frame ceiling inputLimit args (by omega) (by omega) limitBound
      scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget run
  have metadata := evaluateHOLFiniteState_metadata state
    (.call (some (some (.local,ofString "top"),none)) (ofString "rlp_decode_fully") transactionTypedDecodeArguments)
  rw [run] at metadata
  dsimp only at metadata
  have locals : ∀ key, key ≠ ofString "top" → post.locals.lookup key = state.locals.lookup key := by
    intro key different
    apply evaluate_normalLocalFrame key _ _ state post run
    simp [normalLocalFrameSyntax,Ne.symm different]
  have within : length.toNat ≤ inputLength.toNat := by omega
  have costLe := transaction_list_suffix_cost_mono length.toNat inputLength.toNat inputLength.toNat within
  have bounded := transaction_type_assign_suffix_heap_bounded post pointer length scratch frame array input inputLength tx kind oldKind tag (inputLength - 1) ceiling inputLimit
    payloadNoWrap (by omega) limitBound ((globals _).trans scratchGlobal) ((globals _).trans frameGlobal) (metadata.1.trans code)
    orderedFrame framePositive scratchBelow
    (by intro address low high; rw [metadata.2.1]; exact arena address low high)
    ((globals _).trans heap) arrayBound countLimit
    (by intro address low high; rw [metadata.2.1]; exact heapArena address low high)
    (by omega) (by omega) (by omega) (by omega)
    ((locals _ (by decide)).trans txLocal) ((locals _ (by decide)).trans typeLocal) ((locals _ (by decide)).trans byteLocal)
    inputBeforeArray ((locals _ (by decide)).trans countLocal) supported inputBound headerBefore arrayAbove inputBeforeFrame topLocal
    (Nat.le_trans costLe futureBudget)
  exact ⟨Nat.le_trans bounded.1 (Nat.add_le_add_left costLe _),bounded.2⟩

#print axioms transaction_typed_returned_continuation_heap_bounded
end InitECandidate.Runtime
