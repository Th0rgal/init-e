import InitECandidate.Runtime.U256FromBeTailCallBound
import InitECandidate.Runtime.TrapBodyClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def txScalarU256AfterField : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_tx_scalar_u256 with | .decCall _ _ _ _ body => body | _ => .skip

theorem source_txScalarU256_after_field : txScalarU256AfterField =
    .seq (.ite (.cmp .lower (.const 32) (.rfield 1 (.var .local (ofString "f"))))
      (.raise (ofString "TxErr") (.const 13)) .skip)
      (.call none (ofString "u256_from_be") [.rfield 0 (.var .local (ofString "f")),.rfield 1 (.var .local (ofString "f"))]) := by
  simp only [txScalarU256AfterField,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The actual size guard rejects oversized scalar values before conversion;
accepted values and failed byte reads share the same 33-clock bound. -/
theorem evaluate_txScalarU256_after_field_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64)
    (fieldLocal : state.locals.lookup (ofString "f") = some (.rStruct [.val (.word pointer),.val (.word length)]))
    (code : state.code = originalRuntimeCode) (budget : 33 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state txScalarU256AfterField
    state.clock ≤ evaluated.2.clock + 33 ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  have condition : @evalHOLExact 64 F _ state.toExact (fun a => Classical.propDecidable (state.memaddrs a))
      (.cmp .lower (.const 32) (.rfield 1 (.var .local (ofString "f")))) =
      some (.val (.word (if 32 < length.toNat then 1 else 0))) := by
    simp [evalHOLExact,fieldLocal,Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def]
  by_cases small : length.toNat ≤ 32
  · have passed : evaluateHOLFiniteState state
        (.ite (.cmp .lower (.const 32) (.rfield 1 (.var .local (ofString "f"))))
          (.raise (ofString "TxErr") (.const 13)) .skip) = (none,state) := by
      rw [evaluateHOLFiniteState_ite,condition]
      simp [show ¬32 < length.toNat by omega,evaluateHOLFiniteState_skip]
    rw [source_txScalarU256_after_field,evaluateHOLFiniteState_seq_line780,passed]
    have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
        [.rfield 0 (.var .local (ofString "f")),.rfield 1 (.var .local (ofString "f"))] =
        some [.val (.word pointer),.val (.word length)] := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,fieldLocal]
    exact evaluate_u256FromBe_tailCall_bounded state _ pointer length 32 args code small (by decide) budget
  · have failed : evaluateHOLFiniteState state
        (.ite (.cmp .lower (.const 32) (.rfield 1 (.var .local (ofString "f"))))
          (.raise (ofString "TxErr") (.const 13)) .skip) =
        evaluateHOLFiniteState state (.raise (ofString "TxErr") (.const 13)) := by
      rw [evaluateHOLFiniteState_ite,condition]
      simp [show 32 < length.toNat by omega]
    have terminal := evaluate_raise_terminal state (ofString "TxErr") (.const 13)
    have safe := evaluate_raise_no_timeout state (ofString "TxErr") (.const 13)
    have clock := clockPreserving_raise (σ := F) (ofString "TxErr") (.const 13) state
    rw [source_txScalarU256_after_field,evaluateHOLFiniteState_seq_line780,failed]
    cases raised : evaluateHOLFiniteState state (.raise (ofString "TxErr") (.const 13)) with
    | mk result post =>
      rw [raised] at terminal safe clock
      cases result with
      | none => exact False.elim (terminal rfl)
      | some result =>
        dsimp only
        exact ⟨by dsimp only at clock; omega,by dsimp only at clock; omega,safe,terminal⟩

#print axioms evaluate_txScalarU256_after_field_bounded
end InitECandidate.Runtime
