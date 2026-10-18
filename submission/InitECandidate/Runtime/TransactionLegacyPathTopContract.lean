import InitECandidate.Runtime.TransactionTypedPathTopContract
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_legacy_path_normal_top_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (run : evaluateHOLFiniteState state transactionLegacyPath = (none,post)) :
    ∃ tag payloadPointer payload : BitVec 64,
      post.locals.lookup (ofString "top") = some (.rStruct [.val (.word tag),.val (.word payloadPointer),.val (.word payload),.val (.word length)]) ∧
      (tag = 0 ∨ tag = 1) ∧ payload.toNat ≤ length.toNat ∧
      payloadPointer.toNat + payload.toNat ≤ pointer.toNat + length.toNat ∧
      payloadPointer.toNat + payload.toNat < 2^64 ∧ pointer.toNat ≤ payloadPointer.toNat ∧
      post.globals = state.globals := by
  rw [source_transaction_legacy_decode] at run
  obtain ⟨tag,payloadPointer,payload,atTop,tagBound,payloadBound,_,ends,noWrap,starts,globals⟩ :=
    rlpDecodeFully_local_call_runtime_contract state post (ofString "top") transactionLegacyDecodeArguments
      pointer length scratch frame ceiling inputLimit
      (transaction_legacy_decode_arguments state pointer length pointerLocal lengthLocal) inputRange lengthBound limitBound
      scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget run
  refine ⟨tag,payloadPointer,payload,atTop,tagBound,payloadBound,ends,noWrap,starts,?_⟩
  apply HolFiniteMapExact.ext
  funext name
  exact globals name

#print axioms transaction_legacy_path_normal_top_contract
end InitECandidate.Runtime
