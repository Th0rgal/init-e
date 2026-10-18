import InitECandidate.Runtime.U256FromBeFastBound
import InitECandidate.Runtime.TerminalTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem u256FromBe_fast_body_terminal : terminalTail u256FromBeFastBody = true := by
  simp only [u256FromBeFastBody,u256FromBeFastGuard,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- A uniform bound for the complete original converter: byte count on the
general path and four clocks on the aligned 32-byte path. -/
theorem evaluate_u256FromBe_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64) (limit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (lengthBound : length.toNat ≤ limit)
    (four : 4 ≤ limit) (budget : limit ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_u256_from_be)
    state.clock ≤ evaluated.2.clock + limit ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  by_cases general : length ≠ 32 ∨ pointer &&& 7 ≠ 0
  · have bound := evaluate_u256FromBe_general_bounded state pointer length pointerLocal lengthLocal general (by omega)
    exact ⟨Nat.le_trans bound.1 (Nat.add_le_add_left lengthBound _),bound.2⟩
  · have exactLength : length = 32 := by by_contra wrong; exact general (Or.inl wrong)
    have aligned : pointer &&& 7 = 0 := by by_contra wrong; exact general (Or.inr wrong)
    have condition : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address)) u256FromBeFastCondition =
        some (.val (.word 1)) := by
      rw [source_u256FromBe_fast_condition]
      simp [evalHOLExact,evalListHOLExact,pointerLocal,lengthLocal,wordOpHOL,wordOp,valueIsWord,valueWord,
        Compiler.Encoders.Asm.wordCmpHOL]
      simp only [AndOp.and]
      simp_all
    have fast := u256FromBe_fast_body_bounded state code (by omega)
    have terminal := evaluate_terminalTail u256FromBeFastBody u256FromBe_fast_body_terminal state
    rw [source_u256FromBe_body,evaluateHOLFiniteState_seq_line780,source_u256FromBe_fast_guard,
      evaluateHOLFiniteState_ite,condition]
    simp only
    cases run : evaluateHOLFiniteState state u256FromBeFastBody with
    | mk result post =>
      rw [run] at fast terminal
      dsimp only at fast terminal
      cases result with
      | none => exact False.elim (terminal rfl)
      | some result =>
        have enlarged : state.clock ≤ post.clock + limit ∧ post.clock ≤ state.clock ∧
            (some result : Option (PanSemResultExact 64)) ≠ some .timeOut ∧
            (some result : Option (PanSemResultExact 64)) ≠ none :=
          ⟨by omega,fast.2.1,fast.2.2,by simp⟩
        simpa using enlarged

#print axioms evaluate_u256FromBe_body_bounded
end InitECandidate.Runtime
