import InitECandidate.Runtime.RlpItemLongListFinishBound
import InitECandidate.Runtime.RlpErrorCheckFlow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Returning past long-list validation proves that the payload fits after
its header and that the complete consumed length is positive and input-bounded. -/
theorem rlpItem_long_list_finish_return_progress {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (headerLength payload total : BitVec 64) (value : ValueHOL 64)
    (headerLocal : state.locals.lookup (ofString "ll") = some (.val (.word headerLength)))
    (payloadLocal : state.locals.lookup (ofString "n") = some (.val (.word payload)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (headerFits : 1 + headerLength.toNat ≤ total.toNat)
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state rlpItemLongListFinish = (some (.returned value),post)) :
    payload.toNat < total.toNat ∧ 0 < (1 + (headerLength + payload)).toNat ∧
      (1 + (headerLength + payload)).toNat ≤ total.toNat := by
  have fits : payload.toNat ≤ (total - 1 - headerLength).toNat := by
    by_contra bad
    have less : (total - 1 - headerLength).toNat < payload.toNat := by omega
    obtain ⟨firstResult,middle,firstRun,normal,noReturn⟩ := evaluate_rlp_error_check_flow state
      (.cmp .notLower (.const 55) (.var .local (ofString "n"))) 5 code
    have actual := run
    rw [source_rlpItem_long_list_finish] at actual
    change evaluateHOLFiniteState state (.seq
      (.ite (.cmp .notLower (.const 55) (.var .local (ofString "n")))
        (.call (some (none,none)) (ofString "rlp_fail") [.const 5]) .skip)
      (.seq (.ite (.cmp .lower (.op .sub [.op .sub [.var .local (ofString "len"),.const 1],.var .local (ofString "ll")])
        (.var .local (ofString "n"))) (.call (some (none,none)) (ofString "rlp_fail") [.const 3]) .skip)
        rlpItemLongListTail)) = _ at actual
    rw [evaluateHOLFiniteState_seq_line780,firstRun] at actual
    cases firstResult with
    | some stopped => exact False.elim (noReturn value (Prod.mk.inj actual).1)
    | none =>
      have same := normal rfl
      subst middle
      dsimp only at actual
      have subEval : @evalHOLExact 64 F _ state.toExact
          (fun address => Classical.propDecidable (state.memaddrs address))
          (.op .sub [.op .sub [.var .local (ofString "len"),.const 1],.var .local (ofString "ll")]) =
          some (.val (.word (total - 1 - headerLength))) := by
        simp [evalHOLExact,evalListHOLExact,totalLocal,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
      have flag : Compiler.Encoders.Asm.wordCmpHOL .lower (total - 1 - headerLength) payload = true := by
        change decide ((total - 1 - headerLength).toNat < payload.toNat) = true
        exact decide_eq_true less
      have guard : @evalHOLExact 64 F _ state.toExact
          (fun address => Classical.propDecidable (state.memaddrs address))
          (.cmp .lower (.op .sub [.op .sub [.var .local (ofString "len"),.const 1],.var .local (ofString "ll")])
            (.var .local (ofString "n"))) = some (.val (.word 1)) := by
        rw [evalHOLExact,subEval]
        simp only [evalHOLExact,payloadLocal,flag]
        rfl
      rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard] at actual
      simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false] at actual
      have terminal := evaluate_rlpFail_call_terminal state (.const 3) 3 code (by rfl)
      have failure := evaluate_discard_call_no_return state (ofString "rlp_fail") [.const 3] value
      cases called : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "rlp_fail") [.const 3]) with
      | mk result output =>
        rw [called] at terminal failure actual
        dsimp only at terminal failure actual
        cases result with
        | none => exact False.elim (terminal rfl)
        | some stopped => exact False.elim (failure (Prod.mk.inj actual).1)
  have totalPositive : 1 ≤ total.toNat := by omega
  have tailNat : (total - 1).toNat = total.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (by apply BitVec.le_def.mpr; exact totalPositive)]
    rfl
  have headerBelow : headerLength ≤ total - 1 := by
    apply BitVec.le_def.mpr
    rw [tailNat]
    omega
  rw [BitVec.toNat_sub_of_le headerBelow,tailNat] at fits
  have totalLimit := total.isLt
  have innerNat : (headerLength + payload).toNat = headerLength.toNat + payload.toNat := by
    rw [BitVec.toNat_add_of_lt (by omega)]
  have consumed : (1 + (headerLength + payload)).toNat = 1 + headerLength.toNat + payload.toNat := by
    rw [BitVec.toNat_add_of_lt (by rw [innerNat]; change 1 + (headerLength.toNat + payload.toNat) < 2^64; omega),innerNat]
    change 1 + (headerLength.toNat + payload.toNat) = 1 + headerLength.toNat + payload.toNat
    omega
  rw [consumed]
  omega

#print axioms rlpItem_long_list_finish_return_progress
end InitECandidate.Runtime
