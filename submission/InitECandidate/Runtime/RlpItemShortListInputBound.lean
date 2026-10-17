import InitECandidate.Runtime.RlpItemShortListBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A passing source length check places the short-list payload within the
caller's nonwrapping input, including the zero-length payload case. -/
theorem rlpItem_short_list_input_geometry (pointer total payload : BitVec 64)
    (nonzero : total ≠ 0) (inputRange : pointer.toNat + total.toNat < 2^64)
    (fits : payload.toNat ≤ (total - 1).toNat) :
    (pointer + 1).toNat + payload.toNat < 2^64 ∧ payload.toNat < total.toNat := by
  have positive : 0 < total.toNat := by
    by_contra bad
    apply nonzero
    apply BitVec.eq_of_toNat_eq
    simpa using (show total.toNat = 0 by omega)
  rw [BitVec.toNat_sub_of_le (by apply BitVec.le_def.mpr; change 1 ≤ total.toNat; omega)] at fits
  change payload.toNat ≤ total.toNat - 1 at fits
  have cursor : (pointer + 1).toNat = pointer.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by change pointer.toNat + 1 < 2^64; omega)]
    rfl
  rw [cursor]
  omega

#print axioms rlpItem_short_list_input_geometry
theorem evaluate_rlpItem_short_list_input_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer total length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (nonzero : total ≠ 0)
    (inputRange : pointer.toNat + total.toNat < 2^64) (lengthBound : total.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 1 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state rlpItemShortListBody
    state.clock ≤ evaluated.2.clock + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 1) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut := by
  by_cases fits : length.toNat ≤ (total - 1).toNat
  · have geometry := rlpItem_short_list_input_geometry pointer total length nonzero inputRange fits
    exact evaluate_rlpItem_short_list_typed_body_bounded state pointer length scratch frame ceiling inputLimit
      pointerLocal lengthLocal geometry.1 (by omega) limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
  · have less : (total - 1).toNat < length.toNat := by omega
    have guard : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .lower (.op .sub [.var .local (ofString "len"),.const 1]) (.var .local (ofString "n"))) =
        some (.val (.word 1)) := by
      simp [evalHOLExact,evalListHOLExact,totalLocal,lengthLocal,wordOpHOL,wordOp,valueIsWord,valueWord,
        Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]
      simpa [BitVec.toNat_sub,Nat.add_comm] using less
    have bound := evaluate_rlpFail_call_bounded state (.const 3) 3 code (by omega) (by rfl)
    rw [source_rlpItem_short_list_body,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite,guard]
    simp only [show (1 : BitVec 64) ≠ 0 from by decide,if_false]
    cases run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "rlp_fail") [.const 3]) with
    | mk result post =>
      rw [run] at bound
      cases result with
      | none => exact False.elim (bound.2.2 rfl)
      | some stopped =>
        dsimp only at bound ⊢
        exact ⟨by omega,by omega,bound.2.1⟩

#print axioms evaluate_rlpItem_short_list_input_body_bounded
end InitECandidate.Runtime
