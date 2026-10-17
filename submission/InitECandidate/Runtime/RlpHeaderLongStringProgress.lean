import InitECandidate.Runtime.RlpHeaderLongStringFinish
import InitECandidate.Runtime.RlpErrorChecksReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The long-string header shares the exact availability checks of a long
string; successful validation proves positive, input-bounded consumption. -/
theorem rlpHeader_long_string_finish_progress {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer headerLength payload total : BitVec 64) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "ll") = some (.val (.word headerLength)))
    (payloadLocal : state.locals.lookup (ofString "n") = some (.val (.word payload)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (headerFits : 1 + headerLength.toNat ≤ total.toNat)
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state rlpHeaderLongStringFinish = (some (.returned value),post)) :
    payload.toNat < total.toNat ∧ 0 < (1 + (headerLength + payload)).toNat ∧
      (1 + (headerLength + payload)).toNat ≤ total.toNat := by
  rw [source_rlpHeader_long_string_finish] at run
  have checks := evaluate_rlp_error_checks_replace_returned state post rlpItemLongChecks
    rlpHeaderLongStringReturn rlpItemLongReturn value code run
  have returned : evaluateHOLFiniteState state rlpItemLongReturn =
      (some (.returned (rlpItemLongValue pointer headerLength payload)),emptyLocalsHOLFinite state) := by
    simp [rlpItemLongReturn,rlpItemLongValue,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,
      pointerLocal,headerLocal,payloadLocal,wordOpHOL,wordOp,valueIsWord,valueWord,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  have itemRun : evaluateHOLFiniteState state rlpItemLongFinish =
      (some (.returned (rlpItemLongValue pointer headerLength payload)),emptyLocalsHOLFinite state) := by
    rw [source_rlpItem_long_finish,checks,returned]
  exact rlpItem_long_finish_return_progress state (emptyLocalsHOLFinite state) headerLength payload total
    (rlpItemLongValue pointer headerLength payload) headerLocal payloadLocal totalLocal headerFits code itemRun

/-- Successful long-string validation returns the exact header fields at any clock. -/
theorem rlpHeader_long_string_finish_value {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (headerLength payload : BitVec 64) (value : ValueHOL 64)
    (headerLocal : state.locals.lookup (ofString "ll") = some (.val (.word headerLength)))
    (payloadLocal : state.locals.lookup (ofString "n") = some (.val (.word payload)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state rlpHeaderLongStringFinish = (some (.returned value),post)) :
    value = rlpHeaderLongStringValue headerLength payload := by
  rw [source_rlpHeader_long_string_finish] at run
  have tail := evaluate_rlp_error_checks_returned state post rlpItemLongChecks rlpHeaderLongStringReturn value code run
  have returned : evaluateHOLFiniteState state rlpHeaderLongStringReturn =
      (some (.returned (rlpHeaderLongStringValue headerLength payload)),emptyLocalsHOLFinite state) := by
    simp [rlpHeaderLongStringReturn,rlpHeaderLongStringValue,evaluateHOLFiniteState_return,evalHOLExact,evalListHOLExact,
      headerLocal,payloadLocal,wordOpHOL,wordOp,valueIsWord,valueWord,shapeOfHOLExact,sizeOfShapeWithContextHOL]
  exact Option.some.inj (Prod.mk.inj (tail.symm.trans returned)).1 |> PanSemResultExact.returned.inj

#print axioms rlpHeader_long_string_finish_progress
#print axioms rlpHeader_long_string_finish_value
end InitECandidate.Runtime
