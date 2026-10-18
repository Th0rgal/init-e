import InitECandidate.Runtime.StackRemovePathCallBudget
import InitECandidate.Runtime.StackRemovePathComposeBudget
import InitECandidate.Runtime.StackRemovePathLoopBudget
import InitECandidate.Runtime.StackRemoveLeafBudget
import InitECandidate.Runtime.StackRemoveAllocBudget
import InitECandidate.Runtime.StoreConstsBudget

namespace InitECandidate.Runtime.StackRemove
open Flapjack Compiler.Backend.StackLang StackSemEvaluate StackSemStateOps StackSemControl StackSemMeasure
open Flapjack.Compiler.Backend.StackRemove
local macro "normalize_result" r:ident "using" proof:term : tactic =>
  `(tactic| (
    rcases ($proof:term) with ⟨clock, bound, post, run, relation⟩
    refine ⟨clock, ?_, post, run, ?_⟩
    · first | exact bound | omega | (simp only [removePathWork]; omega)
    cases $r:ident with
    | none => exact relation
    | some returned => cases returned <;> exact relation))

/-- Flapjack-only induction infrastructure on the exact evaluator's original
clock-first lexicographic measure. Every recursive premise is discharged at
its actual source call site, using its source guard and clock law. -/
private theorem correctnessMeasure_path {width : Nat} [NeZero width] {C F : Type} :
    ∀ (measure : Nat × Nat) (program : HolProg width) (source : StackSemStateFiniteExact width C F),
      stackSemMeasure program source = measure →
      ∀ (result : Option (StackSemResult width)) (postSource target : StackSemStateFiniteExact width C F)
        (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool),
      ∀ (_hypothesis : evaluate (program, source) = (result, postSource) ∧ result ≠ some .error ∧
        stateRelHOL jump bounds pointer source target ∧ Flapjack.Compiler.Backend.StackProps.regBound program pointer),
      ∃ clock, clock ≤ removePathWork program source ∧ ∃ postTarget,
        evaluate (comp jump bounds pointer program, {target with clock := clock + target.clock}) =
          (result, postTarget) ∧
        (match result with
         | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
         | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  intro measure
  induction measure using Flapjack.Compiler.Backend.StackProps.EvaluateAddClock.lexNat_wf.induction with
  | _ measure ih =>
  intro program source hm result postSource target pointer bounds jump hypothesis
  subst hm
  cases program
  all_goals first
    | solve | refine (by normalize_result result using (MemoryZero.compCorrectFFI _ _ _ _ _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (MemoryZero.compCorrectGet _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (MemoryZero.compCorrectSet _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (MemoryZero.compCorrectBitmapLoad _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (MemoryZero.compCorrectInstall _ _ _ _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (MemoryZero.compCorrectDataBufferWrite _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Zero.compCorrectSkip _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Zero.compCorrectHalt _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Zero.compCorrectAlloc _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (storeConsts_bounded _ _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (MemoryZero.compCorrectStackLoadAny _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (MemoryZero.compCorrectStackStoreAny _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Zero.compCorrectLocValue _ _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Zero.compCorrectTick _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Zero.compCorrectReturn _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Zero.compCorrectRaise _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Zero.compCorrectBreak _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Zero.compCorrectContinue _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (MemoryZero.compCorrectShMemOp _ _ _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (MemoryZero.compCorrectStackFree _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (compCorrectStackAlloc_bounded _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Zero.compCorrectOpCurrHeap _ _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (MemoryZero.compCorrectStackLoad _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (MemoryZero.compCorrectStackStore _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Zero.compCorrectInst _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (Zero.compCorrectCodeBufferWrite _ _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (MemoryZero.compCorrectStackGetSize _ _ _ _ _ _ _ _ hypothesis))
    | solve | refine (by normalize_result result using (MemoryZero.compCorrectStackSetSize _ _ _ _ _ _ _ _ hypothesis))
    | skip
  case seq first second =>
    refine (by normalize_result result using (compCorrectSeq_path_bounded first second source result postSource target pointer bounds jump ?_ ?_ hypothesis))
    · intro r post t k off j h
      normalize_result r using (ih _ (seq_first_measure_lt first second source) first source rfl r post t k off j h)
    · intro middle firstRun
      have smaller := seq_second_measure_lt first second source ((none : Option (StackSemResult width)), middle)
      have unclamped := StackSemEvaluateClock.fixClockEvaluate first source
      rw [firstRun] at unclamped
      rw [unclamped] at smaller
      intro r post t k off j h
      normalize_result r using (ih _ smaller second middle rfl r post t k off j h)
  case ite comparison register operand first second =>
    refine (by normalize_result result using (compCorrectIf_path_bounded comparison register operand first second source result postSource target pointer bounds jump ?_ ?_ hypothesis))
    · intro left right _ _ _ r post t k off j h
      normalize_result r using (ih _ (if_first_measure_lt comparison register operand first second source) first source rfl r post t k off j h)
    · intro left right _ _ _ r post t k off j h
      normalize_result r using (ih _ (if_second_measure_lt comparison register operand first second source) second source rfl r post t k off j h)
  case loop body =>
    refine (by normalize_result result using (compCorrectLoop_path_bounded body source result postSource target pointer bounds jump ?_ ?_ hypothesis))
    · intro r post t k off j h
      normalize_result r using (ih _ (loop_body_measure_lt body source) body source rfl r post t k off j h)
    · intro bodyResult middle bodyRun _ nonzero
      have unclamped := StackSemEvaluateClock.fixClockEvaluate body source
      rw [bodyRun] at unclamped
      have smaller := loop_reentry_measure_lt body source (bodyResult, middle)
        (by simpa only [unclamped] using nonzero)
      rw [unclamped] at smaller
      intro r post t k off j h
      normalize_result r using (ih _ smaller (.loop body) (decClock middle) rfl r post t k off j h)
  case jumpLower first second label =>
    refine (by normalize_result result using (compCorrectJumpLower_path_bounded first second label source result postSource target pointer bounds jump ?_ hypothesis))
    · intro left right program _ _ _ _ nonzero r post t k off j h
      normalize_result r using (ih _ (callee_measure_lt program (.jumpLower first second label) source nonzero) program (decClock source) rfl r post t k off j h)
  case rawCall label =>
    refine (by normalize_result result using (compCorrectRawCall_path_bounded label source result postSource target pointer bounds jump ?_ hypothesis))
    · intro frame body _ nonzero r post t k off j h
      normalize_result r using (ih _ (callee_measure_lt body (.rawCall label) source nonzero) body (decClock source) rfl r post t k off j h)
  case call ret dest handler =>
    refine (by normalize_result result using (compCorrectCall_path_bounded ret dest handler source result postSource target pointer bounds jump ?_ ?_ ?_ hypothesis))
    · cases ret with
      | none =>
        intro program _ _ nonzero r post t k off j h
        normalize_result r using (ih _ (callee_measure_lt program (.call none dest handler) source nonzero) program (decClock source) rfl r post t k off j h)
      | some entry =>
        rcases entry with ⟨body, link, l1, l2⟩
        intro program _ nonzero
        have smaller := callee_measure_lt program (.call (some (body, link, l1, l2)) dest handler)
          (setVar link (.loc l1 l2) source) nonzero
        intro r post t k off j h
        normalize_result r using (ih _ smaller program (decClock (setVar link (.loc l1 l2) source)) rfl r post t k off j h)
    · cases ret with
      | none => trivial
      | some entry =>
        rcases entry with ⟨body, link, l1, l2⟩
        intro program middle _ nonzero calleeRun
        have unclamped := StackSemEvaluateClock.fixClockEvaluate program (decClock (setVar link (.loc l1 l2) source))
        rw [calleeRun] at unclamped
        have smaller := call_continuation_measure_lt body (.call (some (body, link, l1, l2)) dest handler)
          source link l1 l2 ((some (.result (.loc l1 l2)) : Option (StackSemResult width)), middle) nonzero
        rw [unclamped] at smaller
        intro r post t k off j h
        normalize_result r using (ih _ smaller body middle rfl r post t k off j h)
    · cases ret with
      | none => trivial
      | some entry =>
        rcases entry with ⟨body, link, l1, l2⟩
        cases handler with
        | none => trivial
        | some handlerEntry =>
          rcases handlerEntry with ⟨handlerBody, hl1, hl2⟩
          intro program middle _ nonzero calleeRun
          have unclamped := StackSemEvaluateClock.fixClockEvaluate program (decClock (setVar link (.loc l1 l2) source))
          rw [calleeRun] at unclamped
          have smaller := call_continuation_measure_lt handlerBody
            (.call (some (body, link, l1, l2)) dest (some (handlerBody, hl1, hl2)))
            source link l1 l2 ((some (.exception (.loc hl1 hl2)) : Option (StackSemResult width)), middle) nonzero
          rw [unclamped] at smaller
          intro r post t k off j h
          normalize_result r using (ih _ smaller handlerBody middle rfl r post t k off j h)


/-- Full stack-removal simulation with a source-derived extra-clock budget.
A uniform ceiling over challenge inputs is a separate obligation. -/
theorem removePathWork_correct {width : Nat} [NeZero width] {C F : Type}
    (program : HolProg width) (source : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width)) (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : evaluate (program, source) = (result, postSource) ∧ result ≠ some .error ∧
      stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound program pointer) :
    ∃ clock, clock ≤ removePathWork program source ∧ ∃ postTarget,
      evaluate (comp jump bounds pointer program, {target with clock := clock + target.clock}) =
        (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  normalize_result result using (correctnessMeasure_path (stackSemMeasure program source)
    program source rfl result postSource target pointer bounds jump hypothesis)

#print axioms removePathWork_correct
end InitECandidate.Runtime.StackRemove
