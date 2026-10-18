import InitECandidate.Runtime.RlpItemBodyGlobals
import InitECandidate.Runtime.RlpItemBodyRange
import InitECandidate.Runtime.RlpItemBodyNamedGlobal
import InitECandidate.Runtime.RlpItemLoadedGlobals
import InitECandidate.Runtime.RlpErrorCheckFlow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpItem_body_returned_runtime_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92632 ≤ state.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item) = (some (.returned value),post)) :
    ∃ kind payloadPointer payload consumed : BitVec 64,
      value = .rStruct [.val (.word kind),.val (.word payloadPointer),.val (.word payload),.val (.word consumed)] ∧
      pointer.toNat ≤ payloadPointer.toNat ∧
      payloadPointer.toNat + payload.toNat ≤ pointer.toNat + length.toNat ∧
      payloadPointer.toNat + payload.toNat < 2^64 ∧ payload.toNat ≤ length.toNat ∧
      post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
      post.globals.lookup (ofString "heap_ptr") = state.globals.lookup (ofString "heap_ptr") := by
  obtain ⟨kind,payloadPointer,payload,consumed,shape,ends,noWrap,starts⟩ :=
    rlpItem_body_return_range state post pointer length value pointerLocal lengthLocal code
      (by omega) inputRange (by omega) run
  have globals := rlpItem_body_returned_globals state post pointer length scratch frame ceiling inputLimit pointerLocal lengthLocal
    inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget value run
  have heap := rlpItem_body_returned_named_global state post (ofString "heap_ptr") (by decide) pointer length scratch frame
    ceiling inputLimit pointerLocal lengthLocal inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame
    framePositive scratchBelow arena budget value run
  exact ⟨kind,payloadPointer,payload,consumed,shape,starts,ends,noWrap,by omega,globals.1,globals.2,heap⟩

#print axioms rlpItem_body_returned_runtime_contract
end InitECandidate.Runtime
