import InitECandidate.Runtime.TransactionTypedPathBelow
import InitECandidate.Runtime.RlpDecodeFullyLocalCallRuntimeContract
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_typed_path_normal_top_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (run : evaluateHOLFiniteState state transactionTypedPath = (none,post)) :
    ∃ tag payloadPointer payload : BitVec 64,
      post.locals.lookup (ofString "top") = some (.rStruct [.val (.word tag),.val (.word payloadPointer),.val (.word payload),.val (.word (length - 1))]) ∧
      (tag = 0 ∨ tag = 1) ∧ payload.toNat ≤ length.toNat ∧
      payloadPointer.toNat + payload.toNat ≤ pointer.toNat + length.toNat ∧
      payloadPointer.toNat + payload.toNat < 2^64 ∧ pointer.toNat ≤ payloadPointer.toNat ∧
      post.globals = state.globals := by
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
      obtain ⟨tag,payloadPointer,payload,atTop,tagBound,payloadBound,_,ends,noWrap,starts,globals⟩ :=
        rlpDecodeFully_local_call_runtime_contract state middle (ofString "top") transactionTypedDecodeArguments
          (pointer + 1) (length - 1) scratch frame ceiling inputLimit args (by rw [range.2.2.1]; exact inputRange)
          (Nat.le_trans range.2.2.2 lengthBound) limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget called
      have topFrame := evaluate_straight_local_frame (ofString "top") (.seq transactionTypeAssign transactionTypeFields) (by rfl) middle
      have globalFrame := evaluate_readOnly_globals (.seq transactionTypeAssign transactionTypeFields) (by rfl) middle
      rw [run] at topFrame globalFrame
      refine ⟨tag,payloadPointer,payload,topFrame.trans atTop,tagBound,?_,?_,noWrap,?_,?_⟩
      · omega
      · rw [range.2.2.1] at ends
        exact ends
      · rw [range.1] at starts
        omega
      · apply HolFiniteMapExact.ext
        funext name
        exact (congrArg (fun map => map.lookup name) globalFrame).trans (globals name)

#print axioms transaction_typed_path_normal_top_contract
end InitECandidate.Runtime
