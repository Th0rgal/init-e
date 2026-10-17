import InitECandidate.Runtime.RlpItemListChecksGlobals
import InitECandidate.Runtime.RlpItemShortListProgress
import InitECandidate.Runtime.RlpItemPayloadRange
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpItem_short_list_input_body_returned_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer total length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (payloadLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (nonzero : total ≠ 0) (small : length.toNat ≤ 55)
    (inputRange : pointer.toNat + total.toNat < 2^64) (lengthBound : total.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 1 ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state rlpItemShortListBody = (some (.returned value),post)) :
    post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  have progress := rlpItem_short_list_return_progress state post length total value payloadLocal totalLocal
    nonzero small code (by omega) run
  have geometry := rlpItem_payload_pointer_range pointer total 1 length inputRange
    (by omega) (by decide) (by omega) progress.2.2
  exact rlpItem_short_list_body_returned_globals state post
    [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "n")]
    (pointer + 1) length scratch frame ceiling inputLimit rfl
    (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,payloadLocal,
      wordOpHOL,wordOp,valueIsWord,valueWord])
    geometry.2.1 (by omega) limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget value run

#print axioms rlpItem_short_list_input_body_returned_globals
end InitECandidate.Runtime
