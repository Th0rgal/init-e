import InitECandidate.Runtime.HashWordStep
import InitECandidate.Runtime.StraightLineNoTimeout
import InitECandidate.Proofs.FrontendCodecComputation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def commonPrefixLoop : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_common_prefix_length with
  | .decCall _ _ _ _ (.dec _ _ _ (.seq loop _)) => loop
  | _ => .skip

def commonPrefixStep : ProgHOL 64 :=
  match commonPrefixLoop with | .while _ body => body | _ => .skip

def commonPrefixMismatch : ExpHOL 64 :=
  .cmp .notEqual
    (.loadByte (.op .add [.var .local (ofString "a"),.var .local (ofString "i")]))
    (.loadByte (.op .add [.var .local (ofString "b"),.var .local (ofString "i")]))

theorem source_commonPrefix_step : commonPrefixStep =
    .seq (.ite commonPrefixMismatch (.return (.var .local (ofString "i"))) .skip)
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])) := by
  simp only [commonPrefixStep,commonPrefixLoop,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_commonPrefix_loop : commonPrefixLoop =
    .while (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))) commonPrefixStep := by
  simp only [commonPrefixLoop,commonPrefixStep,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- All byte access outcomes are covered: error, return the current mismatch
index, or advance exactly one. None of these consumes nested source clock. -/
theorem evaluate_commonPrefix_step_cases {F : Type} (state : PanSemStateFiniteExact 64 F)
    (index : BitVec 64) (binding : state.locals.lookup (ofString "i") = some (.val (.word index))) :
    evaluateHOLFiniteState state commonPrefixStep = (some .error,state) ∨
    evaluateHOLFiniteState state commonPrefixStep = (some (.returned (.val (.word index))),emptyLocalsHOLFinite state) ∨
    evaluateHOLFiniteState state commonPrefixStep = (none,setVarHOLFinite (ofString "i") (.val (.word (index + 1))) state) := by
  have assigned := evaluate_local_word_assignment state (ofString "i")
    (.op .add [.var .local (ofString "i"),.const 1]) index (index + 1) binding
    (by simp [evalHOLExact,evalListHOLExact,binding,wordOpHOL,wordOp,valueIsWord,valueWord])
  have returned : evaluateHOLFiniteState state (.return (.var .local (ofString "i"))) =
      (some (.returned (.val (.word index))),emptyLocalsHOLFinite state) := by
    simp [evaluateHOLFiniteState_return,evalHOLExact,binding,shapeOfHOLExact]
  rw [source_commonPrefix_step,evaluateHOLFiniteState_seq_line780,evaluateHOLFiniteState_ite]
  cases condition : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address)) commonPrefixMismatch with
  | none => exact Or.inl rfl
  | some value =>
    cases value with
    | rStruct fields => exact Or.inl rfl
    | nStruct name fields => exact Or.inl rfl
    | val value =>
      cases value with
      | word word =>
        by_cases zero : word = 0
        · simp only [if_pos zero,evaluateHOLFiniteState_skip]
          exact Or.inr (Or.inr assigned)
        · simp only [if_neg zero,returned]
          exact Or.inr (Or.inl trivial)

#print axioms source_commonPrefix_step
#print axioms source_commonPrefix_loop
#print axioms evaluate_commonPrefix_step_cases
end InitECandidate.Runtime
