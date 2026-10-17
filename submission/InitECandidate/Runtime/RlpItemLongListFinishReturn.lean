import InitECandidate.Runtime.RlpItemLongListProgress
import InitECandidate.Runtime.RlpItemListReturnFields
import InitECandidate.Runtime.RlpErrorChecksReturnFlow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpItem_long_list_finish_return_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer headerLength payload total : BitVec 64) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "ll") = some (.val (.word headerLength)))
    (payloadLocal : state.locals.lookup (ofString "n") = some (.val (.word payload)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (headerFits : 1 + headerLength.toNat ≤ total.toNat)
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state rlpItemLongListFinish = (some (.returned value),post)) :
    value = .rStruct [.val (.word 1),.val (.word (pointer + (1 + headerLength))),
      .val (.word payload),.val (.word (1 + (headerLength + payload)))] ∧
    payload.toNat < total.toNat ∧ 0 < (1 + (headerLength + payload)).toNat ∧
      (1 + (headerLength + payload)).toNat ≤ total.toNat := by
  have progress := rlpItem_long_list_finish_return_progress state post headerLength payload total value
    headerLocal payloadLocal totalLocal headerFits code run
  rw [source_rlpItem_long_list_finish] at run
  have tail := evaluate_rlp_error_checks_returned_tail state post rlpItemLongChecks rlpItemLongListTail value code run
  exact ⟨rlpItem_long_list_tail_return_contract state post pointer headerLength payload value
    pointerLocal headerLocal payloadLocal tail,progress⟩

#print axioms rlpItem_long_list_finish_return_contract
end InitECandidate.Runtime
