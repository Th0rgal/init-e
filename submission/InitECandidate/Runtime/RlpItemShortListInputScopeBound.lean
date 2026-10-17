import InitECandidate.Runtime.RlpItemShortListInputBound
import InitECandidate.Runtime.RlpItemShortListScopeBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original short-list branch is bounded from the caller's input
range, including payloads that fail its own size check. -/
theorem evaluate_rlpItem_short_list_input_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer total header scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (nonzero : total ≠ 0)
    (inputRange : pointer.toNat + total.toNat < 2^64) (lengthBound : total.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : (header - 192).toNat * ((2 * (header - 192).toNat + 1) * 15 + 19) + 1 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state rlpItemShortList
    state.clock ≤ evaluated.2.clock + ((header - 192).toNat * ((2 * (header - 192).toNat + 1) * 15 + 19) + 1) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  let entered := setVarHOLFinite (ofString "n") (.val (.word (header - 192))) state
  have atPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "n" ≠ ofString "p" by decide] using pointerLocal
  have atLength : entered.locals.lookup (ofString "n") = some (.val (.word (header - 192))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atTotal : entered.locals.lookup (ofString "len") = some (.val (.word total)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "n" ≠ ofString "len" by decide] using totalLocal
  have bound := evaluate_rlpItem_short_list_input_body_bounded entered pointer total (header - 192) scratch frame ceiling inputLimit
    atPointer atLength atTotal nonzero inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .sub [.var .local (ofString "b"),.const 192]) = some (.val (.word (header - 192))) := by
    simp [evalHOLExact,evalListHOLExact,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_rlpItem_short_list,evaluateHOLFiniteState_dec_total]
  simp only [initializer,shapeOfHOLExact,shapeEqHOL,if_true]
  change (let result := evaluateHOLFiniteState entered rlpItemShortListBody; _) ∧ _
  cases run : evaluateHOLFiniteState entered rlpItemShortListBody with
  | mk result post =>
    rw [run] at bound
    exact bound

#print axioms evaluate_rlpItem_short_list_input_bounded
end InitECandidate.Runtime
