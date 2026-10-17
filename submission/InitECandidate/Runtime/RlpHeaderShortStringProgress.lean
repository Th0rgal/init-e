import InitECandidate.Runtime.RlpHeaderShortStringBody
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_rlpHeader_short_string : rlpHeaderShortStringBranch =
    .dec (ofString "n") .one (.op .sub [.var .local (ofString "b"),.const 128]) rlpHeaderShortStringBody := by
  simp only [rlpHeaderShortStringBody,rlpHeaderShortStringBranch,rlpHeaderAfterSingle,rlpHeaderAfterByte,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Returning past the real short-string header size check proves that its payload
fits in the supplied bytes and that the consumed length strictly advances. -/
theorem rlpHeader_short_string_return_progress {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (payload total : BitVec 64) (value : ValueHOL 64)
    (payloadLocal : state.locals.lookup (ofString "n") = some (.val (.word payload)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (nonzero : total ≠ 0) (small : payload.toNat ≤ 55)
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state rlpHeaderShortStringBody = (some (.returned value),post)) :
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
    rw [source_rlpHeader_short_string_body,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard] at run
    simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false] at run
    have bound := evaluate_rlpFail_call_terminal state (.const 3) 3 code (by rfl)
    have noReturn := evaluate_discard_call_no_return state (ofString "rlp_fail") [.const 3] value
    cases called : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "rlp_fail") [.const 3]) with
    | mk result output =>
      rw [called] at bound noReturn run
      dsimp only at bound noReturn run
      cases result with
      | none => exact False.elim (bound rfl)
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

/-- The original payload-length declaration preserves short-string header progress. -/
theorem rlpHeader_short_string_scoped_progress {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (header total : BitVec 64) (value : ValueHOL 64)
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (lower : 128 ≤ header.toNat) (upper : header.toNat ≤ 183)
    (nonzero : total ≠ 0) (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state rlpHeaderShortStringBranch = (some (.returned value),post)) :
    (header - 128).toNat < total.toNat ∧ 0 < (1 + (header - 128)).toNat ∧
      (1 + (header - 128)).toNat ≤ total.toNat := by
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .sub [.var .local (ofString "b"),.const 128]) = some (.val (.word (header - 128))) := by
    simp [evalHOLExact,evalListHOLExact,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_rlpHeader_short_string] at run
  obtain ⟨output,bodyRun,_⟩ := evaluate_dec_word_result_scope state post (ofString "n")
    (.op .sub [.var .local (ofString "b"),.const 128]) (header - 128) rlpHeaderShortStringBody
    (some (.returned value)) initializer run
  let entered := setVarHOLFinite (ofString "n") (.val (.word (header - 128))) state
  have atPayload : entered.locals.lookup (ofString "n") = some (.val (.word (header - 128))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atTotal : entered.locals.lookup (ofString "len") = some (.val (.word total)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "n" ≠ ofString "len" by decide] using totalLocal
  have small : (header - 128).toNat ≤ 55 := by
    rw [BitVec.toNat_sub_of_le (show (128 : BitVec 64) ≤ header from BitVec.le_def.mpr lower)]
    change header.toNat - 128 ≤ 55
    omega
  exact rlpHeader_short_string_return_progress entered output (header - 128) total value
    atPayload atTotal nonzero small code bodyRun

#print axioms rlpHeader_short_string_return_progress
#print axioms rlpHeader_short_string_scoped_progress
end InitECandidate.Runtime
