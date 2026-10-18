import InitECandidate.Runtime.RlpDecodeFullyLocalCallAbove
import InitECandidate.Runtime.TransactionTypedDecodeSource
import InitECandidate.Runtime.TransactionLegacyDecodeSource
import InitECandidate.Runtime.TransactionTypeFieldsFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_typed_path_normal_above {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (budget : (length - 1).toNat * ((2 * (length - 1).toNat + 1) * 15 + 19) + 92634 ≤ state.clock)
    (run : evaluateHOLFiniteState state transactionTypedPath = (none,post)) (address : BitVec 64) (above : ceiling ≤ address.toNat) :
    post.memory address = state.memory address := by
  have range := transaction_typed_decode_range pointer length positive inputRange
  have args := transaction_typed_decode_arguments state pointer length pointerLocal lengthLocal
  rw [source_transaction_typed_decode,evaluateHOLFiniteState_seq_line780] at run
  cases called : evaluateHOLFiniteState state
      (.call (some (some (.local,ofString "top"),none)) (ofString "rlp_decode_fully") transactionTypedDecodeArguments) with
  | mk result middle =>
    rw [called] at run
    cases result with
    | some result => cases run
    | none =>
      dsimp only at run
      have parsed := rlpDecodeFully_local_call_above state middle (ofString "top") transactionTypedDecodeArguments
        (pointer + 1) (length - 1) scratch frame ceiling inputLimit args (by rw [range.2.2.1]; exact inputRange)
        (Nat.le_trans range.2.2.2 lengthBound) limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget called address above
      have remaining := evaluate_readOnly_memory (.seq transactionTypeAssign transactionTypeFields) (by rfl) middle
      rw [run] at remaining
      exact (congrFun remaining address).trans parsed

theorem transaction_legacy_path_normal_above {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92634 ≤ state.clock)
    (run : evaluateHOLFiniteState state transactionLegacyPath = (none,post)) (address : BitVec 64) (above : ceiling ≤ address.toNat) :
    post.memory address = state.memory address := by
  rw [source_transaction_legacy_decode] at run
  exact rlpDecodeFully_local_call_above state post (ofString "top") transactionLegacyDecodeArguments
    pointer length scratch frame ceiling inputLimit
    (transaction_legacy_decode_arguments state pointer length pointerLocal lengthLocal)
    inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget run address above

#print axioms transaction_legacy_path_normal_above
#print axioms transaction_typed_path_normal_above
end InitECandidate.Runtime
