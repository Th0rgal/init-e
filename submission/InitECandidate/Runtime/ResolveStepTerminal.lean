import InitECandidate.Runtime.ResolveStepSource
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_return_ne_none {F : Type} (s : PanSemStateFiniteExact 64 F) (expression : ExpHOL 64) :
    (evaluateHOLFiniteState s (.return expression)).1 ≠ none := by
  rw [evaluateHOLFiniteState_return]
  split <;> simp_all
  split <;> simp

theorem evaluate_sequence_tail_ne_none {F : Type} (s : PanSemStateFiniteExact 64 F) (first tail : ProgHOL 64)
    (terminal : ∀ next : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState next tail).1 ≠ none) :
    (evaluateHOLFiniteState s (.seq first tail)).1 ≠ none := by
  rw [evaluateHOLFiniteState_seq_line780]
  cases firstRun : evaluateHOLFiniteState s first with
  | mk result post =>
    cases result with
    | none => exact terminal post
    | some stopped => simp

theorem evaluate_declared_call_tail_ne_none {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64)) (tail : ProgHOL 64)
    (terminal : ∀ next : PanSemStateFiniteExact 64 F, (evaluateHOLFiniteState next tail).1 ≠ none) :
    (evaluateHOLFiniteState s (.decCall name shape function arguments tail)).1 ≠ none := by
  rw [evaluateHOLFiniteState_decCall_total]
  split
  · simp
  · rename_i values args
    split
    · simp
    · rename_i body callee returnShape lookup
      split
      · simp
      · dsimp only
        cases bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) body with
        | mk result post =>
          dsimp only
          cases result with
          | none => simp
          | some stopped =>
            cases stopped <;> simp only
            all_goals try simp [emptyLocalsHOLFinite]
            split
            · exact terminal _
            · simp

theorem resolve_step_hashed_terminal {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s resolveStepHashed).1 ≠ none := by
  rw [source_resolve_step_hashed]
  exact evaluate_declared_call_tail_ne_none s _ _ _ _ _ (fun next => evaluate_return_ne_none next _)

theorem resolve_step_lookup_tail_terminal {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s resolveStepLookupTail).1 ≠ none := by
  rw [source_resolve_step_lookup_tail]
  exact evaluate_sequence_tail_ne_none s _ _ (fun next => evaluate_return_ne_none next _)

theorem resolve_step_lookup_terminal {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s resolveStepLookup).1 ≠ none := by
  rw [source_resolve_step_lookup]
  exact evaluate_declared_call_tail_ne_none s _ _ _ _ _ resolve_step_lookup_tail_terminal

theorem resolve_step_string_terminal {F : Type} (s : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState s resolveStepStringBranch).1 ≠ none := by
  rw [source_resolve_step_string]
  apply evaluate_sequence_tail_ne_none
  intro next
  exact evaluate_sequence_tail_ne_none next _ _ resolve_step_lookup_terminal

#print axioms evaluate_return_ne_none
#print axioms evaluate_sequence_tail_ne_none
#print axioms evaluate_declared_call_tail_ne_none
#print axioms resolve_step_hashed_terminal
#print axioms resolve_step_lookup_tail_terminal
#print axioms resolve_step_lookup_terminal
#print axioms resolve_step_string_terminal
end InitECandidate.Runtime
