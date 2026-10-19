import InitECandidate.Runtime.DecodeStepKindDispatch
import InitECandidate.Runtime.MptFailCallTerminal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The real nonempty byte-string case rejects through mpt_fail(4), without
entering list construction or claiming a successful parser record. -/
theorem evaluate_decode_step_nonempty_bytes {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer payload consumed : BitVec 64) (nonempty : payload ≠ 0) (code : s.code = originalRuntimeCode)
    (atItem : s.locals.lookup (ofString "it") = some
      (.rStruct [.val (.word (0#64)),.val (.word pointer),.val (.word payload),.val (.word consumed)])) :
    evaluateHOLFiniteState s (decodeStepAt 3) = evaluateHOLFiniteState s
      (.call (some (none,none)) (ofString "mpt_fail") [.const 4]) := by
  rw [source_decode_step_kind_dispatch,evaluateHOLFiniteState_seq_line780]
  simp [decodeStepKindGuard,evaluateHOLFiniteState_ite,evaluateHOLFiniteState_seq_line780,
    evalHOLExact,evalListHOLExact,atItem,Compiler.Encoders.Asm.wordCmpHOL,
    evaluateHOLFiniteState_return,evaluateHOLFiniteState_skip,shapeOfHOLExact]
  rw [if_neg (show payload ≠ 0#64 from nonempty)]
  cases failRun : evaluateHOLFiniteState s (.call (some (none,none)) (ofString "mpt_fail") [.const 4]) with
  | mk result post =>
    cases result with
    | none =>
      have terminal := evaluate_mptFail_call_terminal s (.const 4) 4 code
        (by rw [evalListHOLFinite_eq_toExact]; rfl)
      rw [failRun] at terminal
      exact False.elim (terminal rfl)
    | some result => rfl

/-- The rejecting scalar case has a one-tick bound in every outcome. -/
theorem runBounded_decode_step_nonempty_bytes {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer payload consumed : BitVec 64) (nonempty : payload ≠ 0) (code : s.code = originalRuntimeCode)
    (atItem : s.locals.lookup (ofString "it") = some
      (.rStruct [.val (.word (0#64)),.val (.word pointer),.val (.word payload),.val (.word consumed)]))
    (ticks : s.clock ≠ 0) : RunBounded s (decodeStepAt 3) 1 := by
  unfold RunBounded
  rw [evaluate_decode_step_nonempty_bytes s pointer payload consumed nonempty code atItem]
  have bound := evaluate_mptFail_call_bounded s (.const 4) 4 code ticks
    (by rw [evalListHOLFinite_eq_toExact]; rfl)
  exact ⟨by rw [bound.1]; omega,by rw [bound.1]; omega,bound.2.1⟩

#print axioms evaluate_decode_step_nonempty_bytes
#print axioms runBounded_decode_step_nonempty_bytes
end InitECandidate.Runtime
