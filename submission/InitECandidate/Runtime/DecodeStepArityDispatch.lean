import InitECandidate.Runtime.DecodeStepSlicesRuntimeReach
import InitECandidate.Runtime.DecodeStepBranchScratchProgress
import InitECandidate.Runtime.MptFailCallTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def decodeStepTwoCase : ProgHOL 64 :=
  match decodeStepAt 6 with | .seq (.ite _ body _) _ => body | _ => .skip

theorem source_decode_step_two_dispatch : decodeStepAt 6 =
    .seq (.ite (.cmp .equal (.rfield 1 (.var .local (ofString "sl"))) (.const 2))
      decodeStepTwoCase .skip) (decodeStepAt 7) := by
  simp only [decodeStepAt,decodeStepTwoCase,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_decode_step_branch_dispatch : decodeStepAt 7 =
    .seq (.ite (.cmp .notEqual (.rfield 1 (.var .local (ofString "sl"))) (.const 17))
      (.call (some (none,none)) (ofString "mpt_fail") [.const 4]) .skip)
      decodeStepBranchConstruction := by
  simp only [decodeStepAt,decodeStepBranchConstruction,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem evaluate_decode_step_non_two {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count : BitVec 64) (different : count ≠ 2)
    (atSlices : s.locals.lookup (ofString "sl") = some (.rStruct [.val (.word array),.val (.word count)])) :
    evaluateHOLFiniteState s (decodeStepAt 6) = evaluateHOLFiniteState s (decodeStepAt 7) := by
  rw [source_decode_step_two_dispatch,evaluateHOLFiniteState_seq_line780]
  simp [evaluateHOLFiniteState_ite,evalHOLExact,atSlices,Compiler.Encoders.Asm.wordCmpHOL,
    (show count ≠ 2#64 from different),evaluateHOLFiniteState_skip]

/-- The actual 17-element case reaches branch construction without a clock tick. -/
theorem evaluate_decode_step_seventeen {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array : BitVec 64)
    (atSlices : s.locals.lookup (ofString "sl") = some (.rStruct [.val (.word array),.val (.word (17#64))])) :
    evaluateHOLFiniteState s (decodeStepAt 6) = evaluateHOLFiniteState s decodeStepBranchConstruction := by
  rw [evaluate_decode_step_non_two s array 17 (by decide) atSlices,source_decode_step_branch_dispatch,
    evaluateHOLFiniteState_seq_line780]
  simp [evaluateHOLFiniteState_ite,evalHOLExact,atSlices,Compiler.Encoders.Asm.wordCmpHOL,
    evaluateHOLFiniteState_skip]

/-- Other list arities take the actual rejecting call, never a successful node path. -/
theorem evaluate_decode_step_invalid_arity {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count : BitVec 64) (notTwo : count ≠ 2) (notSeventeen : count ≠ 17)
    (code : s.code = originalRuntimeCode)
    (atSlices : s.locals.lookup (ofString "sl") = some (.rStruct [.val (.word array),.val (.word count)])) :
    evaluateHOLFiniteState s (decodeStepAt 6) = evaluateHOLFiniteState s
      (.call (some (none,none)) (ofString "mpt_fail") [.const 4]) := by
  rw [evaluate_decode_step_non_two s array count notTwo atSlices,source_decode_step_branch_dispatch,
    evaluateHOLFiniteState_seq_line780]
  simp [evaluateHOLFiniteState_ite,evalHOLExact,atSlices,Compiler.Encoders.Asm.wordCmpHOL,(show count ≠ 17#64 from notSeventeen)]
  cases failRun : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "mpt_fail") [.const 4]) with
  | mk result post =>
    cases result with
    | none =>
      have terminal := evaluate_mptFail_call_terminal s (.const 4) 4 code
        (by rw [evalListHOLFinite_eq_toExact]; rfl)
      rw [failRun] at terminal
      exact False.elim (terminal rfl)
    | some result => rfl

theorem runBounded_decode_step_invalid_arity {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array count : BitVec 64) (notTwo : count ≠ 2) (notSeventeen : count ≠ 17)
    (code : s.code = originalRuntimeCode)
    (atSlices : s.locals.lookup (ofString "sl") = some (.rStruct [.val (.word array),.val (.word count)]))
    (ticks : s.clock ≠ 0) : RunBounded s (decodeStepAt 6) 1 := by
  unfold RunBounded
  rw [evaluate_decode_step_invalid_arity s array count notTwo notSeventeen code atSlices]
  have bound := evaluate_mptFail_call_bounded s (.const 4) 4 code ticks
    (by rw [evalListHOLFinite_eq_toExact]; rfl)
  exact ⟨by rw [bound.1]; omega,by rw [bound.1]; omega,bound.2.1⟩

#print axioms runBounded_decode_step_invalid_arity
#print axioms source_decode_step_two_dispatch
#print axioms source_decode_step_branch_dispatch
#print axioms evaluate_decode_step_non_two
#print axioms evaluate_decode_step_seventeen
#print axioms evaluate_decode_step_invalid_arity
end InitECandidate.Runtime
