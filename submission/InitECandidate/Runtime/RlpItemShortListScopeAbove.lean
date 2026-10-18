import InitECandidate.Runtime.RlpItemShortListInputAbove
import InitECandidate.Runtime.RlpItemShortListScopeBound
import InitECandidate.Runtime.PanDecWordResultScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpItem_short_list_returned_above {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer total header scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (nonzero : total ≠ 0) (lower : 192 ≤ header.toNat) (upper : header.toNat ≤ 247)
    (inputRange : pointer.toNat + total.toNat < 2^64) (lengthBound : total.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : (header - 192).toNat * ((2 * (header - 192).toNat + 1) * 15 + 19) + 1 ≤ state.clock)
    (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state rlpItemShortList = (some (.returned value),post)) (address : BitVec 64) (above : ceiling ≤ address.toNat) :
    post.memory address = state.memory address := by
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .sub [.var .local (ofString "b"),.const 192]) = some (.val (.word (header - 192))) := by
    simp [evalHOLExact,evalListHOLExact,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_rlpItem_short_list] at run
  obtain ⟨output,bodyRun,restored⟩ := evaluate_dec_word_result_scope state post (ofString "n")
    (.op .sub [.var .local (ofString "b"),.const 192]) (header - 192) rlpItemShortListBody
    (some (.returned value)) initializer run
  let entered := setVarHOLFinite (ofString "n") (.val (.word (header - 192))) state
  have atPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "n" ≠ ofString "p" by decide] using pointerLocal
  have atPayload : entered.locals.lookup (ofString "n") = some (.val (.word (header - 192))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atTotal : entered.locals.lookup (ofString "len") = some (.val (.word total)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "n" ≠ ofString "len" by decide] using totalLocal
  have small : (header - 192).toNat ≤ 55 := by
    rw [BitVec.toNat_sub_of_le (by apply BitVec.le_def.mpr; exact lower)]
    change header.toNat - 192 ≤ 55
    omega
  have globals := rlpItem_short_list_input_body_returned_above entered output pointer total (header - 192) scratch frame ceiling inputLimit
    atPointer atPayload atTotal nonzero small inputRange lengthBound limitBound scratchGlobal frameGlobal code
    orderedFrame framePositive scratchBelow arena budget value bodyRun address above
  rw [restored]
  exact globals

#print axioms rlpItem_short_list_returned_above
end InitECandidate.Runtime
