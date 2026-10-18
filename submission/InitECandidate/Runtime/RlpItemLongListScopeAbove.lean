import InitECandidate.Runtime.RlpItemLongListBodyAbove
import InitECandidate.Runtime.RlpItemLongListScopeBound
import InitECandidate.Runtime.PanDecWordResultScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpItem_long_list_returned_above {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (pointer total header scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (inputRange : pointer.toNat + total.toNat < 2^64)
    (nonzero : total ≠ 0)
    (lower : 247 < header.toNat) (upper : header.toNat ≤ 255)
    (lengthBound : total.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (ticks : (header - 247).toNat + 2 + (total.toNat * ((2 * total.toNat + 1) * 15 + 19) + 1) ≤ state.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state rlpItemLongList = (some (.returned value),final)) (address : BitVec 64) (above : ceiling ≤ address.toNat) :
    final.memory address = state.memory address := by
  have sizeBound : (header - 247).toNat ≤ 8 := by
    rw [BitVec.toNat_sub_of_le (by apply BitVec.le_def.mpr; change 247 ≤ header.toNat; omega)]
    change header.toNat - 247 ≤ 8
    omega
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .sub [.var .local (ofString "b"),.const 247]) = some (.val (.word (header - 247))) := by
    simp [evalHOLExact,evalListHOLExact,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_rlpItem_long_list] at run
  obtain ⟨output,bodyRun,restored⟩ := evaluate_dec_word_result_scope state final (ofString "ll")
    (.op .sub [.var .local (ofString "b"),.const 247]) (header - 247) rlpItemLongListBody
    (some (.returned value)) initializer run
  let entered := setVarHOLFinite (ofString "ll") (.val (.word (header - 247))) state
  have atPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "ll" ≠ ofString "p" by decide] using pointerLocal
  have atLength : entered.locals.lookup (ofString "ll") = some (.val (.word (header - 247))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atTotal : entered.locals.lookup (ofString "len") = some (.val (.word total)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "ll" ≠ ofString "len" by decide] using totalLocal
  have globals := rlpItem_long_list_body_returned_above entered output pointer total (header - 247) scratch frame ceiling inputLimit
    atPointer atLength atTotal inputRange nonzero sizeBound lengthBound limitBound scratchGlobal frameGlobal
    code orderedFrame framePositive scratchBelow arena ticks value bodyRun address above
  rw [restored]
  exact globals

#print axioms rlpItem_long_list_returned_above
end InitECandidate.Runtime
