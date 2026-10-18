import InitECandidate.Runtime.RlpItemLongListReadAbove
import InitECandidate.Runtime.RlpItemLongListBodyReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpItem_long_list_body_returned_above {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (pointer total headerLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "ll") = some (.val (.word headerLength)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (inputRange : pointer.toNat + total.toNat < 2^64)
    (nonzero : total ≠ 0)
    (headerBound : headerLength.toNat ≤ 8)
    (lengthBound : total.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (ticks : headerLength.toNat + 2 + (total.toNat * ((2 * total.toNat + 1) * 15 + 19) + 1) ≤ state.clock) (value : ValueHOL 64)
    (evaluated : evaluateHOLFiniteState state rlpItemLongListBody = (some (.returned value),final)) (address : BitVec 64) (above : ceiling ≤ address.toNat) :
    final.memory address = state.memory address := by
  have headerFits := rlpItem_long_list_body_header_fits state final headerLength total value
    headerLocal totalLocal nonzero code (by omega) evaluated
  obtain ⟨result,middle,checked,normal,noReturn⟩ := evaluate_rlp_error_check_flow state
    (.cmp .lower (.op .sub [.var .local (ofString "len"),.const 1]) (.var .local (ofString "ll"))) 3 code
  rw [source_rlpItem_long_list_body,evaluateHOLFiniteState_seq_line780,checked] at evaluated
  cases result with
  | some stopped => exact False.elim (noReturn value (Prod.mk.inj evaluated).1)
  | none =>
    have same := normal rfl
    subst middle
    exact rlpItem_long_list_read_returned_above state final pointer total headerLength scratch frame ceiling inputLimit
      pointerLocal headerLocal totalLocal inputRange headerFits headerBound lengthBound limitBound scratchGlobal frameGlobal
      code orderedFrame framePositive scratchBelow arena ticks value evaluated address above

#print axioms rlpItem_long_list_body_returned_above
end InitECandidate.Runtime
