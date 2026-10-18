import InitECandidate.Runtime.GlobalsFrameComposition
import InitECandidate.Runtime.LookupCodeInstalledBody
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Evaluation from the original code keeps every global whenever the entry
globals satisfy `guard`. -/
def GuardedGlobalsFrame (guard : HolFiniteMapExact MlS (ValueHOL 64) → Prop) (program : ProgHOL 64) : Prop :=
  ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode → guard state.globals →
    (evaluateHOLFiniteState state program).2.globals = state.globals

namespace GuardedGlobalsFrame
variable {guard : HolFiniteMapExact MlS (ValueHOL 64) → Prop}

theorem of_original {program : ProgHOL 64} (frame : OriginalGlobalsFrame program) :
    GuardedGlobalsFrame guard program := fun state code _ => frame state code

theorem seq {first second : ProgHOL 64} (a : GuardedGlobalsFrame guard first)
    (b : GuardedGlobalsFrame guard second) : GuardedGlobalsFrame guard (.seq first second) := by
  intro F state code holds
  have globals := a state code holds
  have metadata := evaluateHOLFiniteState_metadata state first
  rw [evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState state first with
  | mk result middle =>
    rw [run] at globals metadata
    cases result with
    | none => exact (b middle (metadata.1.trans code) (by rw [globals]; exact holds)).trans globals
    | some _ => exact globals

theorem ite (condition : ExpHOL 64) {yes no : ProgHOL 64} (a : GuardedGlobalsFrame guard yes)
    (b : GuardedGlobalsFrame guard no) : GuardedGlobalsFrame guard (.ite condition yes no) := by
  intro F state code holds
  rw [evaluateHOLFiniteState_ite]
  split
  · split
    · exact b state code holds
    · exact a state code holds
  · rfl

/-- Discard (`some (none,none)`) and tail (`none`) calls keep globals when the
installed body does from the callee entry state. -/
theorem call (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL 64)))
    (handlerFree : info = none ∨ info = some (none,none))
    (function : MlS) (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (frame : GuardedGlobalsFrame guard body) (arguments : List (ExpHOL 64)) :
    GuardedGlobalsFrame guard (.call info function arguments) := by
  intro F state code holds
  rw [evaluateHOLFiniteState_call]
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => rfl
  | some values =>
    dsimp only
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => rfl
    | some data =>
      obtain ⟨foundBody,locals,foundShape⟩ := data
      dsimp only
      by_cases zero : state.clock = 0
      · simp [zero,emptyLocalsHOLFinite]
      · rw [if_neg zero]
        have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body foundBody
          returnShape foundShape values locals (by rw [code]; exact installed) lookup
        have globals := frame (callEntryStateHOLFinite state locals) code holds
        rw [← same] at globals
        cases run : evaluateHOLFiniteState (callEntryStateHOLFinite state locals) foundBody with
        | mk result post =>
          rw [run] at globals
          change post.globals = state.globals at globals
          rcases handlerFree with h | h <;> subst h
          all_goals
            cases result with
            | none => exact globals
            | some result =>
              cases result <;> simp_all [emptyLocalsHOLFinite]
              all_goals (split <;> simp_all)

theorem decCall (function : MlS) (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (frame : GuardedGlobalsFrame guard body) (name : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64))
    {continuation : ProgHOL 64} (rest : GuardedGlobalsFrame guard continuation) :
    GuardedGlobalsFrame guard (.decCall name shape function arguments continuation) := by
  intro F state code holds
  rw [evaluateHOLFiniteState_decCall_total]
  cases args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments with
  | none => rfl
  | some values =>
    dsimp only
    cases lookup : lookupCodeHOLFinite state.code.lookup function values with
    | none => rfl
    | some data =>
      obtain ⟨foundBody,locals,foundShape⟩ := data
      dsimp only
      by_cases zero : state.clock = 0
      · simp [zero,emptyLocalsHOLFinite]
      · rw [if_neg zero]
        have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body foundBody
          returnShape foundShape values locals (by rw [code]; exact installed) lookup
        have globals := frame (callEntryStateHOLFinite state locals) code holds
        have metadata := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state locals) body
        rw [← same] at globals metadata
        cases run : evaluateHOLFiniteState (callEntryStateHOLFinite state locals) foundBody with
        | mk result post =>
          rw [run] at globals metadata
          change post.globals = state.globals at globals
          dsimp only [fixClockHOLFinite]
          cases result with
          | none => exact globals
          | some result =>
            cases result
            all_goals first
              | (simp [emptyLocalsHOLFinite]; exact globals)
              | skip
            rename_i w
            dsimp only
            split
            · rw [rest _ (by exact metadata.1.trans code) (by change guard post.globals; rw [globals]; exact holds)]
              exact globals
            · exact globals

end GuardedGlobalsFrame

#print axioms GuardedGlobalsFrame.seq
#print axioms GuardedGlobalsFrame.ite
#print axioms GuardedGlobalsFrame.call
#print axioms GuardedGlobalsFrame.decCall
end InitECandidate.Runtime
