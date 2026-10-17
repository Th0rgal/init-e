import InitECandidate.Runtime.RlpItemListReturnFields
import InitECandidate.Runtime.RlpItemShortListProgress
import InitECandidate.Runtime.RlpErrorCheckFlow
import InitECandidate.Runtime.RlpItemShortListScopeBound
import InitECandidate.Runtime.PanDecWordResultScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successful original short-list body returns its exact item fields
and consumes a positive number of bytes within the supplied input. -/
theorem rlpItem_short_list_body_return_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer payload total : BitVec 64) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (payloadLocal : state.locals.lookup (ofString "n") = some (.val (.word payload)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (nonzero : total ≠ 0) (small : payload.toNat ≤ 55)
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpItemShortListBody = (some (.returned value),post)) :
    value = .rStruct [.val (.word 1),.val (.word (pointer + 1)),.val (.word payload),.val (.word (1 + payload))] ∧
      payload.toNat < total.toNat ∧ 0 < (1 + payload).toNat ∧ (1 + payload).toNat ≤ total.toNat := by
  have progress := rlpItem_short_list_return_progress state post payload total value payloadLocal totalLocal nonzero small code ticks run
  obtain ⟨result,middle,checked,normal,noReturn⟩ := evaluate_rlp_error_check_flow state
    (.cmp .lower (.op .sub [.var .local (ofString "len"),.const 1]) (.var .local (ofString "n"))) 3 code
  rw [source_rlpItem_short_list_body,evaluateHOLFiniteState_seq_line780,checked] at run
  cases result with
  | some stopped => exact False.elim (noReturn value (Prod.mk.inj run).1)
  | none =>
    have same := normal rfl
    subst middle
    exact ⟨rlpItem_short_list_tail_return_contract state post pointer payload value pointerLocal payloadLocal run,progress⟩

#print axioms rlpItem_short_list_body_return_contract

/-- The original payload declaration preserves the body return contract
through restoration of its old local binding. -/
theorem rlpItem_short_list_return_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer header total : BitVec 64) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (lower : 192 ≤ header.toNat) (upper : header.toNat ≤ 247)
    (nonzero : total ≠ 0) (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpItemShortList = (some (.returned value),post)) :
    value = .rStruct [.val (.word 1),.val (.word (pointer + 1)),.val (.word (header - 192)),.val (.word (1 + (header - 192)))] ∧
      (header - 192).toNat < total.toNat ∧ 0 < (1 + (header - 192)).toNat ∧
      (1 + (header - 192)).toNat ≤ total.toNat := by
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .sub [.var .local (ofString "b"),.const 192]) = some (.val (.word (header - 192))) := by
    simp [evalHOLExact,evalListHOLExact,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_rlpItem_short_list] at run
  obtain ⟨output,bodyRun,_⟩ := evaluate_dec_word_result_scope state post (ofString "n")
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
  exact rlpItem_short_list_body_return_contract entered output pointer (header - 192) total value
    atPointer atPayload atTotal nonzero small code ticks bodyRun

#print axioms rlpItem_short_list_return_contract
end InitECandidate.Runtime
