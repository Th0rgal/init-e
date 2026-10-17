import InitECandidate.Runtime.RlpItemLongListFinishBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Passing both availability checks puts the decoded long-list payload
inside the original nonwrapping caller input. -/
theorem rlpItem_long_list_input_geometry (pointer total headerLength payload : BitVec 64)
    (inputRange : pointer.toNat + total.toNat < 2^64)
    (headerFits : 1 + headerLength.toNat ≤ total.toNat)
    (payloadFits : payload.toNat ≤ (total - 1 - headerLength).toNat) :
    (pointer + (1 + headerLength)).toNat + payload.toNat < 2^64 ∧
      payload.toNat < total.toNat := by
  have tailNat : (total - 1).toNat = total.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (by apply BitVec.le_def.mpr; change 1 ≤ total.toNat; omega)]
    rfl
  have headerBelow : headerLength ≤ total - 1 := by
    apply BitVec.le_def.mpr
    rw [tailNat]
    omega
  rw [BitVec.toNat_sub_of_le headerBelow,tailNat] at payloadFits
  have innerNat : (1 + headerLength).toNat = 1 + headerLength.toNat := by
    rw [BitVec.toNat_add_of_lt (by change 1 + headerLength.toNat < 2^64; have := total.isLt; omega)]
    rfl
  have cursor : (pointer + (1 + headerLength)).toNat = pointer.toNat + 1 + headerLength.toNat := by
    rw [BitVec.toNat_add_of_lt (by rw [innerNat]; omega),innerNat]
    omega
  rw [cursor]
  omega

#print axioms rlpItem_long_list_input_geometry
theorem evaluate_rlpItem_long_list_input_finish_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer total headerLength length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "ll") = some (.val (.word headerLength)))
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (inputRange : pointer.toNat + total.toNat < 2^64)
    (headerFits : 1 + headerLength.toNat ≤ total.toNat)
    (lengthBound : total.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 1 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state rlpItemLongListFinish
    state.clock ≤ evaluated.2.clock + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 1) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  by_cases fits : length.toNat ≤ (total - 1 - headerLength).toNat
  · have geometry := rlpItem_long_list_input_geometry pointer total headerLength length inputRange headerFits fits
    exact evaluate_rlpItem_long_list_finish_bounded state
      [.op .add [.var .local (ofString "p"),.const 1,.var .local (ofString "ll")],.var .local (ofString "n")]
      (pointer + (1 + headerLength)) length scratch frame ceiling inputLimit rfl
      (by simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,headerLocal,lengthLocal,
        wordOpHOL,wordOp,valueIsWord,valueWord])
      geometry.1 (by omega) limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
  · have less : (total - 1 - headerLength).toNat < length.toNat := by omega
    have subEval : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.op .sub [.op .sub [.var .local (ofString "len"),.const 1],.var .local (ofString "ll")]) =
        some (.val (.word (total - 1 - headerLength))) := by
      simp [evalHOLExact,evalListHOLExact,totalLocal,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
    have flag : Compiler.Encoders.Asm.wordCmpHOL .lower (total - 1 - headerLength) length = true := by
      change decide ((total - 1 - headerLength).toNat < length.toNat) = true
      exact decide_eq_true less
    have guard : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .lower (.op .sub [.op .sub [.var .local (ofString "len"),.const 1],.var .local (ofString "ll")])
          (.var .local (ofString "n"))) = some (.val (.word 1)) := by
      rw [evalHOLExact,subEval]
      simp only [evalHOLExact,lengthLocal,flag]
      rfl
    obtain ⟨result,post,run,cost,remaining,noTimeout,normal,_⟩ := evaluate_rlp_error_check state
      (.cmp .notLower (.const 55) (.var .local (ofString "n"))) 5 code (by omega)
    rw [source_rlpItem_long_list_finish]
    simp only [rlpErrorChecks,rlpItemLongChecks,List.foldr]
    rw [evaluateHOLFiniteState_seq_line780,run]
    cases result with
    | some stopped =>
      dsimp only
      exact ⟨by omega,remaining,noTimeout⟩
    | none =>
      have same := normal rfl
      subst post
      dsimp only
      rw [evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard]
      simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false]
      have failed := evaluate_rlpFail_call_bounded state (.const 3) 3 code (by omega) (by rfl)
      cases called : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "rlp_fail") [.const 3]) with
      | mk result output =>
        rw [called] at failed
        cases result with
        | none => exact False.elim (failed.2.2 rfl)
        | some stopped =>
          dsimp only at failed ⊢
          exact ⟨by omega,by omega,failed.2.1⟩

#print axioms evaluate_rlpItem_long_list_input_finish_bounded
end InitECandidate.Runtime
