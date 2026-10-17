import InitECandidate.Runtime.RlpItemLongBodyBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Returning past long-string validation proves that the payload fits after
its header and that the complete consumed length is positive and input-bounded. -/
theorem rlpItem_long_finish_return_progress {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (headerLength payload total : BitVec 64) (value : ValueHOL 64)
    (headerLocal : state.locals.lookup (ofString "ll") = some (.val (.word headerLength)))
    (payloadLocal : state.locals.lookup (ofString "n") = some (.val (.word payload)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (headerFits : 1 + headerLength.toNat ≤ total.toNat)
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpItemLongFinish = (some (.returned value),post)) :
    payload.toNat < total.toNat ∧ 0 < (1 + (headerLength + payload)).toNat ∧
      (1 + (headerLength + payload)).toNat ≤ total.toNat := by
  have fits : payload.toNat ≤ (total - 1 - headerLength).toNat := by
    by_contra bad
    have less : (total - 1 - headerLength).toNat < payload.toNat := by omega
    obtain ⟨firstResult,middle,firstRun,_,_,_,normal,noReturn,_,_⟩ := evaluate_rlp_error_check state
      (.cmp .notLower (.const 55) (.var .local (ofString "n"))) 5 code ticks
    have actual := run
    rw [source_rlpItem_long_finish] at actual
    change evaluateHOLFiniteState state (.seq
      (.ite (.cmp .notLower (.const 55) (.var .local (ofString "n")))
        (.call (some (none,none)) (ofString "rlp_fail") [.const 5]) .skip)
      (.seq (.ite (.cmp .lower (.op .sub [.op .sub [.var .local (ofString "len"),.const 1],.var .local (ofString "ll")])
        (.var .local (ofString "n"))) (.call (some (none,none)) (ofString "rlp_fail") [.const 3]) .skip)
        rlpItemLongReturn)) = _ at actual
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
      have bound := evaluate_rlpFail_call_bounded state (.const 3) 3 code (by omega) (by rfl)
      have failure := evaluate_discard_call_no_return state (ofString "rlp_fail") [.const 3] value
      cases called : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "rlp_fail") [.const 3]) with
      | mk result output =>
        rw [called] at bound failure actual
        dsimp only at bound failure actual
        cases result with
        | none => exact False.elim (bound.2.2 rfl)
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

/-- Returning past the outer original availability check proves that the
length-of-length itself fits before payload decoding begins. -/
theorem rlpItem_long_body_header_fits {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (headerLength total : BitVec 64) (value : ValueHOL 64)
    (headerLocal : state.locals.lookup (ofString "ll") = some (.val (.word headerLength)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (nonzero : total ≠ 0) (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpItemLongBody = (some (.returned value),post)) :
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
    rw [source_rlpItem_long_body,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard] at run
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

#print axioms rlpItem_long_body_header_fits
#print axioms rlpItem_long_finish_return_progress
end InitECandidate.Runtime
