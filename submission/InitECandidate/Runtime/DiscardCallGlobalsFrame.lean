import InitECandidate.Runtime.GlobalsFrameComposition
import InitECandidate.Runtime.LookupCodeInstalledBody
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A handler-free discard call retains globals when its installed body does,
including malformed arguments, clock exhaustion and interrupted callee outcomes. -/
theorem originalGlobalsFrame_discard_call (function : MlS) (parameters : List (MlS × ShapeHOL))
    (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (frame : OriginalGlobalsFrame body) (arguments : List (ExpHOL 64)) :
    OriginalGlobalsFrame (.call (some (none,none)) function arguments) := by
  intro F state code
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
        have globals := frame (callEntryStateHOLFinite state locals) code
        rw [← same] at globals
        cases run : evaluateHOLFiniteState (callEntryStateHOLFinite state locals) foundBody with
        | mk result post =>
          rw [run] at globals
          change post.globals = state.globals at globals
          cases result with
          | none => exact globals
          | some result =>
            cases result <;> simp_all [emptyLocalsHOLFinite]
            split <;> simp_all

#print axioms originalGlobalsFrame_discard_call
end InitECandidate.Runtime
