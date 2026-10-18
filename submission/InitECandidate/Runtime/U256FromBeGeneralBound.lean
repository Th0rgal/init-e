import InitECandidate.Runtime.U256FromBeInitializationBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def u256FromBeFastCondition : ExpHOL 64 :=
  match u256FromBeFastGuard with | .ite condition _ _ => condition | _ => .const 0
def u256FromBeFastBody : ProgHOL 64 :=
  match u256FromBeFastGuard with | .ite _ body _ => body | _ => .skip

theorem source_u256FromBe_fast_guard : u256FromBeFastGuard =
    .ite u256FromBeFastCondition u256FromBeFastBody .skip := by
  simp only [u256FromBeFastGuard,u256FromBeFastCondition,u256FromBeFastBody,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_u256FromBe_fast_condition : u256FromBeFastCondition =
    .op .and [.cmp .notEqual (.const 0) (.cmp .equal (.var .local (ofString "n")) (.const 32)),
        .cmp .notEqual (.const 0) (.cmp .equal (.op .and [.var .local (ofString "p"),.const 7]) (.const 0))] := by
  simp only [u256FromBeFastCondition,u256FromBeFastGuard,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- All lengths other than 32, and all unaligned pointers, execute the actual
bounded general path. Failed byte reads remain within the same bound. -/
theorem evaluate_u256FromBe_general_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "n") = some (.val (.word length)))
    (general : length ≠ 32 ∨ pointer &&& 7 ≠ 0)
    (budget : length.toNat ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_u256_from_be)
    state.clock ≤ evaluated.2.clock + length.toNat ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  have condition : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) u256FromBeFastCondition =
      some (.val (.word 0)) := by
    rw [source_u256FromBe_fast_condition]
    rcases general with wrongLength | unaligned
    · simp [evalHOLExact,evalListHOLExact,pointerLocal,lengthLocal,wordOpHOL,wordOp,valueIsWord,valueWord,
        Compiler.Encoders.Asm.wordCmpHOL]
      simp only [AndOp.and]
      simp_all
    · simp [evalHOLExact,evalListHOLExact,pointerLocal,lengthLocal,wordOpHOL,wordOp,valueIsWord,valueWord,
        Compiler.Encoders.Asm.wordCmpHOL]
      have mask : AndOp.and (7#64) (18446744073709551615#64) = 7#64 := by decide
      rw [mask]
      simp only [AndOp.and]
      simp_all
  have skipped : evaluateHOLFiniteState state u256FromBeFastGuard = (none,state) := by
    rw [source_u256FromBe_fast_guard,evaluateHOLFiniteState_ite,condition]
    simp [evaluateHOLFiniteState_skip]
  rw [source_u256FromBe_body,evaluateHOLFiniteState_seq_line780,skipped]
  exact evaluate_u256FromBe_initialized_bounded state length lengthLocal budget

#print axioms evaluate_u256FromBe_general_bounded
end InitECandidate.Runtime
