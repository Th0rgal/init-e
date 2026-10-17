import InitECandidate.Runtime.RlpItemLongListReadReturn
import InitECandidate.Runtime.RlpItemLongListBodyBound
import InitECandidate.Runtime.RlpErrorCheckFlow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpItem_long_list_body_header_fits {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (headerLength total : BitVec 64) (value : ValueHOL 64)
    (headerLocal : state.locals.lookup (ofString "ll") = some (.val (.word headerLength)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (nonzero : total ≠ 0) (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpItemLongListBody = (some (.returned value),post)) :
    1 + headerLength.toNat ≤ total.toNat := by
  have fits : headerLength.toNat ≤ (total - 1).toNat := by
    by_contra bad
    have less : (total - 1).toNat < headerLength.toNat := by omega
    have subEval : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.op .sub [.var .local (ofString "len"),.const 1]) = some (.val (.word (total - 1))) := by
      simp [evalHOLExact,evalListHOLExact,totalLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
    have flag : Compiler.Encoders.Asm.wordCmpHOL .lower (total - 1) headerLength = true := by
      change decide ((total - 1).toNat < headerLength.toNat) = true
      exact decide_eq_true less
    have guard : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .lower (.op .sub [.var .local (ofString "len"),.const 1]) (.var .local (ofString "ll"))) =
        some (.val (.word 1)) := by
      rw [evalHOLExact,subEval]
      simp only [evalHOLExact,headerLocal,flag]
      rfl
    rw [source_rlpItem_long_list_body,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard] at run
    simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false] at run
    have bound := evaluate_rlpFail_call_bounded state (.const 3) 3 code (by omega) (by rfl)
    have failure := evaluate_discard_call_no_return state (ofString "rlp_fail") [.const 3] value
    cases called : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "rlp_fail") [.const 3]) with
    | mk result output =>
      rw [called] at bound failure run
      dsimp only at bound failure run
      cases result with
      | none => exact False.elim (bound.2.2 rfl)
      | some stopped => exact False.elim (failure (Prod.mk.inj run).1)
  have positive : 1 ≤ total.toNat := by
    by_contra h
    apply nonzero
    apply BitVec.eq_of_toNat_eq
    simpa using (show total.toNat = 0 by omega)
  rw [BitVec.toNat_sub_of_le (by apply BitVec.le_def.mpr; exact positive)] at fits
  change headerLength.toNat ≤ total.toNat - 1 at fits
  omega

theorem rlpItem_long_list_body_return_contract {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (pointer headerLength total : BitVec 64) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "ll") = some (.val (.word headerLength)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (nonzero : total ≠ 0) (code : state.code = originalRuntimeCode)
    (ticks : headerLength.toNat + 2 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpItemLongListBody = (some (.returned value),final)) :
    ∃ payload : BitVec 64,
      value = .rStruct [.val (.word 1),.val (.word (pointer + (1 + headerLength))),
        .val (.word payload),.val (.word (1 + (headerLength + payload)))] ∧
      payload.toNat < total.toNat ∧
      0 < (1 + (headerLength + payload)).toNat ∧ (1 + (headerLength + payload)).toNat ≤ total.toNat := by
  have headerFits := rlpItem_long_list_body_header_fits state final headerLength total value
    headerLocal totalLocal nonzero code (by omega) run
  obtain ⟨result,middle,check,normal,noReturn⟩ := evaluate_rlp_error_check_flow state
    (.cmp .lower (.op .sub [.var .local (ofString "len"),.const 1]) (.var .local (ofString "ll"))) 3 code
  rw [source_rlpItem_long_list_body,evaluateHOLFiniteState_seq_line780,check] at run
  cases result with
  | some stopped => exact False.elim (noReturn value (Prod.mk.inj run).1)
  | none =>
    have same := normal rfl
    subst middle
    exact rlpItem_long_list_read_return_contract state final pointer headerLength total value
      pointerLocal headerLocal totalLocal headerFits code ticks run

#print axioms rlpItem_long_list_body_header_fits
#print axioms rlpItem_long_list_body_return_contract
end InitECandidate.Runtime
