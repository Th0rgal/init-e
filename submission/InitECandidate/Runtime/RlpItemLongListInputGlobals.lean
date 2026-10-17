import InitECandidate.Runtime.RlpItemListChecksGlobals
import InitECandidate.Runtime.RlpItemLongListProgress
import InitECandidate.Runtime.RlpItemPayloadRange
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpItem_long_list_input_finish_returned_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer total headerLength length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "ll") = some (.val (.word headerLength)))
    (payloadLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (headerFits : 1 + headerLength.toNat ≤ total.toNat) (headerBound : headerLength.toNat ≤ 8)
    (inputRange : pointer.toNat + total.toNat < 2^64) (lengthBound : total.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 1 ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state rlpItemLongListFinish = (some (.returned value),post)) :
    post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  have progress := rlpItem_long_list_finish_return_progress state post headerLength length total value
    headerLocal payloadLocal totalLocal headerFits code run
  have headerSmall : (1 + headerLength).toNat ≤ 9 := by
    rw [BitVec.toNat_add_of_lt (by change 1 + headerLength.toNat < 2^64; omega)]
    change 1 + headerLength.toNat ≤ 9
    omega
  have geometry := rlpItem_payload_pointer_range pointer total (1 + headerLength) length inputRange
    (by omega) headerSmall (by omega) (by simpa [BitVec.add_assoc] using progress.2.2)
  exact rlpItem_long_list_finish_returned_globals state post
    [.op .add [.var .local (ofString "p"),.const 1,.var .local (ofString "ll")],.var .local (ofString "n")]
    (pointer + (1 + headerLength)) length scratch frame ceiling inputLimit rfl
    (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,headerLocal,payloadLocal,
      wordOpHOL,wordOp,valueIsWord,valueWord])
    geometry.2.1 (by omega) limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget value run

#print axioms rlpItem_long_list_input_finish_returned_globals
theorem rlpItem_long_list_uniform_finish_returned_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer total headerLength length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "ll") = some (.val (.word headerLength)))
    (payloadLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (headerFits : 1 + headerLength.toNat ≤ total.toNat) (headerBound : headerLength.toNat ≤ 8)
    (inputRange : pointer.toNat + total.toNat < 2^64) (lengthBound : total.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : total.toNat * ((2 * total.toNat + 1) * 15 + 19) + 1 ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state rlpItemLongListFinish = (some (.returned value),post)) :
    post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  have progress := rlpItem_long_list_finish_return_progress state post headerLength length total value
    headerLocal payloadLocal totalLocal headerFits code run
  have smaller : length.toNat * ((2 * length.toNat + 1) * 15 + 19) ≤
      total.toNat * ((2 * total.toNat + 1) * 15 + 19) :=
    Nat.mul_le_mul (by omega) (by omega)
  exact rlpItem_long_list_input_finish_returned_globals state post pointer total headerLength length scratch frame ceiling inputLimit
    pointerLocal headerLocal payloadLocal totalLocal headerFits headerBound inputRange lengthBound limitBound scratchGlobal frameGlobal
    code orderedFrame framePositive scratchBelow arena (by omega) value run

#print axioms rlpItem_long_list_uniform_finish_returned_globals
end InitECandidate.Runtime
