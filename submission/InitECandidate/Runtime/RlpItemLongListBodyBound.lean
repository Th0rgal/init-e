import InitECandidate.Runtime.RlpItemLongListReadBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_rlpItem_long_list_body : rlpItemLongListBody =
    .seq (.ite (.cmp .lower (.op .sub [.var .local (ofString "len"),.const 1])
      (.var .local (ofString "ll")))
      (.call (some (none,none)) (ofString "rlp_fail") [.const 3]) .skip)
      rlpItemLongListRead := by
  simp only [rlpItemLongListRead,rlpItemLongListBody,rlpItemLongList,rlpItemAfterLongString,
    rlpItemAfterShortString,rlpItemAfterSingleByte,rlpItemAfterByte,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem evaluate_rlpItem_long_list_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer total headerLength scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "ll") = some (.val (.word headerLength)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (inputRange : pointer.toNat + total.toNat < 2^64)
    (nonzero : total ≠ 0)
    (lengthBound : total.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (ticks : headerLength.toNat + 2 + (total.toNat * ((2 * total.toNat + 1) * 15 + 19) + 1) ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state rlpItemLongListBody
    state.clock ≤ evaluated.2.clock + (headerLength.toNat + 2 + (total.toNat * ((2 * total.toNat + 1) * 15 + 19) + 1)) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have positive : 1 ≤ total.toNat := by
    by_contra bad
    apply nonzero
    apply BitVec.eq_of_toNat_eq
    simpa using (show total.toNat = 0 by omega)
  have tailNat : (total - 1).toNat = total.toNat - 1 := by
    rw [BitVec.toNat_sub_of_le (by apply BitVec.le_def.mpr; exact positive)]
    rfl
  by_cases fits : 1 + headerLength.toNat ≤ total.toNat
  · have tail := evaluate_rlpItem_long_list_read_bounded state pointer total headerLength scratch frame ceiling inputLimit
      pointerLocal headerLocal totalLocal inputRange fits lengthBound limitBound scratchGlobal frameGlobal code
      orderedFrame framePositive scratchBelow arena ticks
    obtain ⟨result,post,run,cost,remaining,noTimeout,normal,_⟩ := evaluate_rlp_error_check state
      (.cmp .lower (.op .sub [.var .local (ofString "len"),.const 1]) (.var .local (ofString "ll"))) 3 code (by omega)
    rw [source_rlpItem_long_list_body,evaluateHOLFiniteState_seq_line780,run]
    cases result with
    | none =>
      have same := normal rfl
      subst post
      exact tail
    | some stopped =>
      dsimp only
      exact ⟨by omega,remaining,noTimeout⟩
  · have less : (total - 1).toNat < headerLength.toNat := by omega
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
    have failed := evaluate_rlpFail_call_bounded state (.const 3) 3 code (by omega) (by rfl)
    rw [source_rlpItem_long_list_body,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard]
    simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false]
    cases run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "rlp_fail") [.const 3]) with
    | mk result post =>
      rw [run] at failed
      cases result with
      | none => exact False.elim (failed.2.2 rfl)
      | some stopped =>
        dsimp only at failed ⊢
        exact ⟨by omega,by omega,failed.2.1⟩

#print axioms evaluate_rlpItem_long_list_body_bounded
end InitECandidate.Runtime
