import InitECandidate.Runtime.NamedGlobalFrame
import InitECandidate.Runtime.PanEvaluationMetadata
import InitECandidate.Runtime.TrapPrimitiveClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

def OriginalGlobalsFrame (program : ProgHOL 64) : Prop :=
  ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
    (evaluateHOLFiniteState state program).2.globals = state.globals

theorem originalGlobalsFrame_leaf (program : ProgHOL 64)
    (supported : ∀ watched, avoidsGlobalAssignment watched program = true) : OriginalGlobalsFrame program := by
  intro F state _
  apply HolFiniteMapExact.ext
  funext watched
  exact evaluate_avoidsGlobalAssignment watched program (supported watched) state

theorem originalGlobalsFrame_sequence (first second : ProgHOL 64)
    (a : OriginalGlobalsFrame first) (b : OriginalGlobalsFrame second) : OriginalGlobalsFrame (.seq first second) := by
  intro F state code
  have globals := a state code
  have metadata := evaluateHOLFiniteState_metadata state first
  rw [evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState state first with
  | mk result middle =>
    rw [run] at globals metadata
    cases result with
    | none => exact (b middle (metadata.1.trans code)).trans globals
    | some _ => exact globals

theorem originalGlobalsFrame_declaration (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64)
    (body : ProgHOL 64) (frame : OriginalGlobalsFrame body) : OriginalGlobalsFrame (.dec name shape initializer body) := by
  intro F state code
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · rfl
  · split
    · exact frame _ code
    · rfl

theorem originalGlobalsFrame_conditional (condition : ExpHOL 64) (yes no : ProgHOL 64)
    (a : OriginalGlobalsFrame yes) (b : OriginalGlobalsFrame no) : OriginalGlobalsFrame (.ite condition yes no) := by
  intro F state code
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact b state code
    · exact a state code
  · rfl

theorem evaluate_while_globals_frame (condition : ExpHOL 64) (body : ProgHOL 64)
    (frame : OriginalGlobalsFrame body) {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state (.while condition body)).2.globals = state.globals := by
  rw [evaluateHOLFiniteState_while_total]
  split
  · split
    · split
      · rfl
      · rename_i nonzero
        dsimp only
        rw [fixClockHOLFinite_evaluateState]
        have globals := frame (decClockHOLFinite state) code
        have metadata := evaluateHOLFiniteState_metadata (decClockHOLFinite state) body
        have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
        cases run : evaluateHOLFiniteState (decClockHOLFinite state) body with
        | mk result middle =>
          rw [run] at globals metadata remaining
          have smaller : middle.clock < state.clock := by
            change middle.clock ≤ state.clock - 1 at remaining
            omega
          cases result with
          | none => exact (evaluate_while_globals_frame condition body frame middle (metadata.1.trans code)).trans globals
          | some result =>
            cases result with
            | «continue» => exact (evaluate_while_globals_frame condition body frame middle (metadata.1.trans code)).trans globals
            | «break» => exact globals
            | returned _ => exact globals
            | exception _ _ => exact globals
            | finalFfi _ => exact globals
            | error => exact globals
            | timeOut => exact globals
    · rfl
  · rfl
termination_by state.clock

theorem originalGlobalsFrame_while (condition : ExpHOL 64) (body : ProgHOL 64)
    (frame : OriginalGlobalsFrame body) : OriginalGlobalsFrame (.while condition body) :=
  evaluate_while_globals_frame condition body frame

theorem originalGlobalsFrame_external (name : MlS) (a b c d : ExpHOL 64) :
    OriginalGlobalsFrame (.extCall name a b c d) := by
  intro F state _
  rw [evaluateHOLFiniteState_extCall_source]
  repeat first | split | rfl

#print axioms originalGlobalsFrame_leaf
#print axioms originalGlobalsFrame_sequence
#print axioms originalGlobalsFrame_declaration
#print axioms originalGlobalsFrame_conditional
#print axioms originalGlobalsFrame_while
#print axioms originalGlobalsFrame_external
end InitECandidate.Runtime
