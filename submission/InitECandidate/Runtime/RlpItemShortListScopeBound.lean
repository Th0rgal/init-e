import InitECandidate.Runtime.RlpItemShortListBound
import InitECandidate.Runtime.PanSequenceTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_rlpItem_short_list : rlpItemShortList =
    .dec (ofString "n") .one (.op .sub [.var .local (ofString "b"),.const 192]) rlpItemShortListBody := by
  simp only [rlpItemShortList,rlpItemShortListBody,rlpItemAfterLongString,rlpItemAfterShortString,
    rlpItemAfterSingleByte,rlpItemAfterByte,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Binding the actual short-list payload length costs no source ticks and
restores the caller's old local on every outcome. -/
theorem evaluate_rlpItem_short_list_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer header scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (noWrap : (pointer + 1).toNat + (header - 192).toNat < 2^64) (lengthBound : (header - 192).toNat ≤ inputLimit)
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
  have bound := evaluate_rlpItem_short_list_typed_body_bounded entered pointer (header - 192) scratch frame ceiling inputLimit
    atPointer atLength noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
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

#print axioms evaluate_rlpItem_short_list_bounded

/-- Both rejection and successful list validation terminate the original
short-list branch; no input or arena assumptions are needed for this fact. -/
theorem evaluate_rlpItem_short_list_terminal {F : Type} (state : PanSemStateFiniteExact 64 F)
    (header : BitVec 64)
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header))) :
    (evaluateHOLFiniteState state rlpItemShortList).1 ≠ none := by
  have terminal : ∀ current : PanSemStateFiniteExact 64 F,
      (evaluateHOLFiniteState current rlpItemShortListBody).1 ≠ none := by
    intro current
    rw [source_rlpItem_short_list_body]
    apply evaluate_seq_terminal
    intro middle
    rw [source_rlpItem_short_list_tail]
    apply evaluate_seq_terminal
    intro final
    exact evaluate_return_terminal final _
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .sub [.var .local (ofString "b"),.const 192]) = some (.val (.word (header - 192))) := by
    simp [evalHOLExact,evalListHOLExact,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_rlpItem_short_list,evaluateHOLFiniteState_dec_total]
  simp only [initializer,shapeOfHOLExact,shapeEqHOL,if_true]
  let entered := setVarHOLFinite (ofString "n") (.val (.word (header - 192))) state
  cases run : evaluateHOLFiniteState entered rlpItemShortListBody with
  | mk result post =>
    change result ≠ none
    have stopped := terminal entered
    rw [run] at stopped
    exact stopped

#print axioms evaluate_rlpItem_short_list_terminal
end InitECandidate.Runtime
