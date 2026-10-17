import InitECandidate.Runtime.RlpItemLongListFinishBound
import InitECandidate.Runtime.DiscardCallSuccessLocals
import InitECandidate.Runtime.DiscardCallNoReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original short-list count call restores caller locals before the
four-word item return; its memory effects do not affect returned fields. -/
theorem rlpItem_short_list_tail_return_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer payload : BitVec 64) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (payloadLocal : state.locals.lookup (ofString "n") = some (.val (.word payload)))
    (run : evaluateHOLFiniteState state rlpItemShortListTail = (some (.returned value),post)) :
    value = .rStruct [.val (.word 1),.val (.word (pointer + 1)),.val (.word payload),.val (.word (1 + payload))] := by
  have noReturn := evaluate_discard_call_no_return state (ofString "rlp_list_count") [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "n")] value
  rw [source_rlpItem_short_list_tail,evaluateHOLFiniteState_seq_line780] at run
  cases called : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "rlp_list_count") [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "n")]) with
  | mk result middle =>
    rw [called] at run noReturn
    cases result with
    | some stopped => exact False.elim (noReturn (Prod.mk.inj run).1)
    | none =>
      have locals := evaluate_discard_call_success_locals state (ofString "rlp_list_count") [.op .add [.var .local (ofString "p"),.const 1],.var .local (ofString "n")]
        (by rw [called])
      rw [called] at locals
      dsimp only at locals run
      have atPointer : middle.locals.lookup (ofString "p") = some (.val (.word pointer)) := by rw [locals]; exact pointerLocal
      have atPayload : middle.locals.lookup (ofString "n") = some (.val (.word payload)) := by rw [locals]; exact payloadLocal
      have returned : evaluateHOLFiniteState middle
          (.return (.rstruct [.const 1,.op .add [.var .local (ofString "p"),.const 1],
            .var .local (ofString "n"),.op .add [.const 1,.var .local (ofString "n")]])) =
          (some (.returned (.rStruct [.val (.word 1),.val (.word (pointer + 1)),.val (.word payload),.val (.word (1 + payload))])),emptyLocalsHOLFinite middle) := by
        simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,atPointer,atPayload,
          wordOpHOL,wordOp,valueIsWord,valueWord,shapeOfHOLExact,sizeOfShapeWithContextHOL]
      rw [returned] at run
      simpa using (Prod.mk.inj run).1.symm

#print axioms rlpItem_short_list_tail_return_contract
/-- The original long-list count call restores caller locals before the
four-word item return; its memory effects do not affect returned fields. -/
theorem rlpItem_long_list_tail_return_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer headerLength payload : BitVec 64) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "ll") = some (.val (.word headerLength)))
    (payloadLocal : state.locals.lookup (ofString "n") = some (.val (.word payload)))
    (run : evaluateHOLFiniteState state rlpItemLongListTail = (some (.returned value),post)) :
    value = .rStruct [.val (.word 1),.val (.word (pointer + (1 + headerLength))),.val (.word payload),.val (.word (1 + (headerLength + payload)))] := by
  have noReturn := evaluate_discard_call_no_return state (ofString "rlp_list_count") [.op .add [.var .local (ofString "p"),.const 1,.var .local (ofString "ll")],.var .local (ofString "n")] value
  rw [source_rlpItem_long_list_tail,evaluateHOLFiniteState_seq_line780] at run
  cases called : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "rlp_list_count") [.op .add [.var .local (ofString "p"),.const 1,.var .local (ofString "ll")],.var .local (ofString "n")]) with
  | mk result middle =>
    rw [called] at run noReturn
    cases result with
    | some stopped => exact False.elim (noReturn (Prod.mk.inj run).1)
    | none =>
      have locals := evaluate_discard_call_success_locals state (ofString "rlp_list_count") [.op .add [.var .local (ofString "p"),.const 1,.var .local (ofString "ll")],.var .local (ofString "n")]
        (by rw [called])
      rw [called] at locals
      dsimp only at locals run
      have atPointer : middle.locals.lookup (ofString "p") = some (.val (.word pointer)) := by rw [locals]; exact pointerLocal
      have atHeader : middle.locals.lookup (ofString "ll") = some (.val (.word headerLength)) := by rw [locals]; exact headerLocal
      have atPayload : middle.locals.lookup (ofString "n") = some (.val (.word payload)) := by rw [locals]; exact payloadLocal
      have returned : evaluateHOLFiniteState middle
          (.return (.rstruct [.const 1,.op .add [.var .local (ofString "p"),.const 1,.var .local (ofString "ll")],
            .var .local (ofString "n"),.op .add [.const 1,.var .local (ofString "ll"),.var .local (ofString "n")]])) =
          (some (.returned (.rStruct [.val (.word 1),.val (.word (pointer + (1 + headerLength))),.val (.word payload),.val (.word (1 + (headerLength + payload)))])),emptyLocalsHOLFinite middle) := by
        simp [evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,atPointer,atPayload,atHeader,
          wordOpHOL,wordOp,valueIsWord,valueWord,shapeOfHOLExact,sizeOfShapeWithContextHOL]
      rw [returned] at run
      simpa using (Prod.mk.inj run).1.symm

#print axioms rlpItem_long_list_tail_return_contract
end InitECandidate.Runtime
