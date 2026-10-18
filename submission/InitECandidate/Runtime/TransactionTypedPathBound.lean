import InitECandidate.Runtime.TransactionTypedDecodeSource
import InitECandidate.Runtime.RlpDecodeFullyCallBound
import InitECandidate.Runtime.PanSeqStraightBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_typed_path_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (positive : 0 < length.toNat)
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : (length - 1).toNat * ((2 * (length - 1).toNat + 1) * 15 + 19) + 92635 ≤ state.clock)
 :
    let output := evaluateHOLFiniteState state transactionTypedPath
    state.clock ≤ output.2.clock + ((length - 1).toNat * ((2 * (length - 1).toNat + 1) * 15 + 19) + 92635) ∧
      output.2.clock ≤ state.clock ∧ output.1 ≠ some .timeOut := by
  have range := transaction_typed_decode_range pointer length positive inputRange
  have args := transaction_typed_decode_arguments state pointer length pointerLocal lengthLocal
  have parsed := evaluate_rlpDecodeFully_call_bounded state (some (.local,ofString "top")) transactionTypedDecodeArguments
    (pointer + 1) (length - 1) scratch frame ceiling inputLimit args (by rw [range.2.2.1]; exact inputRange)
    (Nat.le_trans range.2.2.2 lengthBound) limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
  rw [source_transaction_typed_decode]
  exact evaluate_sequence_straight_bounded state _ (.seq transactionTypeAssign transactionTypeFields) _ parsed (by rfl)

#print axioms transaction_typed_path_bounded
end InitECandidate.Runtime
