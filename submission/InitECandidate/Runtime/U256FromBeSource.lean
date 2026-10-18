import InitECandidate.Proofs.FrontendCodecComputation
import InitECandidate.Runtime.StraightLineNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def u256FromBeFastGuard : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_u256_from_be with | .seq guard _ => guard | _ => .skip
def u256FromBeInitialized : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_u256_from_be with | .seq _ body => body | _ => .skip
def u256FromBeLoopAndReturn : ProgHOL 64 :=
  match u256FromBeInitialized with
  | .dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ (.dec _ _ _ body)))) => body
  | _ => .skip
def u256FromBeLoop : ProgHOL 64 :=
  match u256FromBeLoopAndReturn with | .seq body _ => body | _ => .skip
def u256FromBeStep : ProgHOL 64 :=
  match u256FromBeLoop with | .while _ body => body | _ => .skip

theorem source_u256FromBe_body : sourceFunctionBody Guest.guestFn_u256_from_be =
    .seq u256FromBeFastGuard u256FromBeInitialized := by
  simp only [u256FromBeFastGuard,u256FromBeInitialized,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_u256FromBe_initialized : u256FromBeInitialized =
    .dec (ofString "l0") .one (.const 0) (.dec (ofString "l1") .one (.const 0)
      (.dec (ofString "l2") .one (.const 0) (.dec (ofString "l3") .one (.const 0)
        (.dec (ofString "i") .one (.const 0) u256FromBeLoopAndReturn)))) := by
  simp only [u256FromBeInitialized,u256FromBeLoopAndReturn,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_u256FromBe_loop_and_return : u256FromBeLoopAndReturn =
    .seq u256FromBeLoop (.return (.rstruct [.var .local (ofString "l0"),
      .var .local (ofString "l1"),.var .local (ofString "l2"),.var .local (ofString "l3")])) := by
  simp only [u256FromBeLoopAndReturn,u256FromBeInitialized,u256FromBeLoop,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_u256FromBe_loop : u256FromBeLoop =
    .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) u256FromBeStep := by
  simp only [u256FromBeLoop,u256FromBeLoopAndReturn,u256FromBeInitialized,u256FromBeStep,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem u256FromBe_step_straight : straightLine u256FromBeStep = true := by
  simp only [u256FromBeStep,u256FromBeLoop,u256FromBeLoopAndReturn,u256FromBeInitialized,
    sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- The actual general-path byte conversion body has no nested clock-consuming
calls or loops, even when a byte load or local expression fails. -/
theorem evaluate_u256FromBe_step_clock {F : Type} (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state u256FromBeStep).2.clock = state.clock ∧
      (evaluateHOLFiniteState state u256FromBeStep).1 ≠ some .timeOut :=
  ⟨clockPreserving_of_straightLine _ u256FromBe_step_straight state,
    evaluate_straightLine_no_timeout _ u256FromBe_step_straight state⟩

#print axioms evaluate_u256FromBe_step_clock
end InitECandidate.Runtime
