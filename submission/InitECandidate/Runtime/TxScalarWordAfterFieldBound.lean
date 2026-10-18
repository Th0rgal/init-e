import InitECandidate.Runtime.TxScalarWordInitializationBound
import InitECandidate.Runtime.TrapBodyClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual size guard rejects oversized scalar values before conversion;
accepted values and failed byte reads share the same eight-clock bound. -/
theorem evaluate_txScalarWord_after_field_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64)
    (fieldLocal : state.locals.lookup (ofString "f") = some (.rStruct [.val (.word pointer),.val (.word length)]))
    (budget : 8 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state txScalarWordAfterField
    state.clock ≤ evaluated.2.clock + 8 ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  have condition : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
      (.cmp .lower (.const 8) (.rfield 1 (.var .local (ofString "f")))) =
      some (.val (.word (if 8 < length.toNat then 1 else 0))) := by
    simp [evalHOLExact,fieldLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]
  by_cases small : length.toNat ≤ 8
  · have passed : evaluateHOLFiniteState state
        (.ite (.cmp .lower (.const 8) (.rfield 1 (.var .local (ofString "f"))))
          (.raise (ofString "TxErr") (.var .local (ofString "envcode"))) .skip) = (none,state) := by
      rw [evaluateHOLFiniteState_ite,condition]
      simp [show ¬8 < length.toNat by omega,evaluateHOLFiniteState_skip]
    rw [source_txScalarWord_after_field,evaluateHOLFiniteState_seq_line780,passed]
    exact evaluate_txScalarWord_initialized_bounded state pointer length fieldLocal small budget
  · have failed : evaluateHOLFiniteState state
        (.ite (.cmp .lower (.const 8) (.rfield 1 (.var .local (ofString "f"))))
          (.raise (ofString "TxErr") (.var .local (ofString "envcode"))) .skip) =
        evaluateHOLFiniteState state (.raise (ofString "TxErr") (.var .local (ofString "envcode"))) := by
      rw [evaluateHOLFiniteState_ite,condition]
      simp [show 8 < length.toNat by omega]
    have terminal := evaluate_raise_terminal state (ofString "TxErr") (.var .local (ofString "envcode"))
    have safe := evaluate_raise_no_timeout state (ofString "TxErr") (.var .local (ofString "envcode"))
    have clock := clockPreserving_raise (σ := F) (ofString "TxErr") (.var .local (ofString "envcode")) state
    rw [source_txScalarWord_after_field,evaluateHOLFiniteState_seq_line780,failed]
    cases raised : evaluateHOLFiniteState state (.raise (ofString "TxErr") (.var .local (ofString "envcode"))) with
    | mk result post =>
      rw [raised] at terminal safe clock
      cases result with
      | none => exact False.elim (terminal rfl)
      | some result =>
        dsimp only
        exact ⟨by dsimp only at clock; omega,by dsimp only at clock; omega,safe,terminal⟩

#print axioms evaluate_txScalarWord_after_field_bounded
end InitECandidate.Runtime
