import InitECandidate.Runtime.RlpItemShortBody
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Returning past the real short-string size check proves that its payload
fits in the supplied bytes and that the consumed length strictly advances. -/
theorem rlpItem_short_return_progress {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (payload total : BitVec 64) (value : ValueHOL 64)
    (payloadLocal : state.locals.lookup (ofString "n") = some (.val (.word payload)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (nonzero : total ≠ 0) (small : payload.toNat ≤ 55)
    (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpItemShortBody = (some (.returned value),post)) :
    payload.toNat < total.toNat ∧ 0 < (1 + payload).toNat ∧ (1 + payload).toNat ≤ total.toNat := by
  have fits : payload.toNat ≤ (total - 1).toNat := by
    by_contra bad
    have less : (total - 1).toNat < payload.toNat := by omega
    have guard : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .lower (.op .sub [.var .local (ofString "len"),.const 1]) (.var .local (ofString "n"))) =
        some (.val (.word 1)) := by
      simp [evalHOLExact,evalListHOLExact,totalLocal,payloadLocal,wordOpHOL,wordOp,valueIsWord,valueWord,
        Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]
      simpa [BitVec.toNat_sub,Nat.add_comm] using less
    rw [source_rlpItem_short_body,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard] at run
    simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false] at run
    have bound := evaluate_rlpFail_call_bounded state (.const 3) 3 code (by omega) (by rfl)
    have noReturn := evaluate_discard_call_no_return state (ofString "rlp_fail") [.const 3] value
    cases called : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "rlp_fail") [.const 3]) with
    | mk result output =>
      rw [called] at bound noReturn run
      dsimp only at bound noReturn run
      cases result with
      | none => exact False.elim (bound.2.2 rfl)
      | some stopped =>
        exact False.elim (noReturn (Prod.mk.inj run).1)
  have positive : 0 < total.toNat := by
    by_contra h
    apply nonzero
    apply BitVec.eq_of_toNat_eq
    simpa using (show total.toNat = 0 by omega)
  rw [BitVec.toNat_sub_of_le (by apply BitVec.le_def.mpr; change 1 ≤ total.toNat; omega)] at fits
  have consumed : (1 + payload).toNat = 1 + payload.toNat := by
    rw [BitVec.toNat_add_of_lt (by change 1 + payload.toNat < 2^64; omega)]
    rfl
  rw [consumed]
  change payload.toNat ≤ total.toNat - 1 at fits
  omega

#print axioms rlpItem_short_return_progress
end InitECandidate.Runtime
