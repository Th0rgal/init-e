import InitECandidate.Runtime.OriginalRlpWriterCode
import InitECandidate.Runtime.DiscardCallGlobalsFrame
import InitECandidate.Runtime.KeccakGlobalsFrame
import InitECandidate.Runtime.AllocationRound
import InitECandidate.Runtime.AllocationSuccess
import InitECandidate.Runtime.RlpEncodeWordWindow
import InitECandidate.Runtime.RlpEncodeBytesPrefix
import InitECandidate.Runtime.RlpFinishList
import InitECandidate.Runtime.RlpHeaderLenMemoryFrame
import InitECandidate.Runtime.RlpWriteHeaderWindow
import InitECandidate.Runtime.RlpPutBeWindow
import InitECandidate.Runtime.RlpEncodeListHeader
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- A tail call that binds nothing, into a globals-retaining installed body, retains globals. -/
theorem originalGlobalsFrame_tail_call (function : MlS)
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (frame : OriginalGlobalsFrame body) (arguments : List (ExpHOL 64)) :
    OriginalGlobalsFrame (.call none function arguments) := by
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
        have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body
          foundBody returnShape foundShape values locals (by rw [code]; exact installed) lookup
        have globals := frame (callEntryStateHOLFinite state locals) code
        rw [← same] at globals
        cases run : evaluateHOLFiniteState (callEntryStateHOLFinite state locals) foundBody with
        | mk result post =>
          rw [run] at globals
          change post.globals = state.globals at globals
          cases result with
          | none => exact globals
          | some result =>
            cases result <;> dsimp only
            all_goals (try split) <;> all_goals (try split) <;> all_goals
              (first
                | exact globals
                | (simp only [setKvarHOLFinite,setVarHOLFinite,emptyLocalsHOLFinite]; exact globals))

/-- A call binding its result to a local retains globals when the installed body does. -/
theorem originalGlobalsFrame_local_call (name function : MlS)
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (frame : OriginalGlobalsFrame body) (arguments : List (ExpHOL 64)) :
    OriginalGlobalsFrame (.call (some ((some (.local,name)),none)) function arguments) := by
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
        have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body
          foundBody returnShape foundShape values locals (by rw [code]; exact installed) lookup
        have globals := frame (callEntryStateHOLFinite state locals) code
        rw [← same] at globals
        cases run : evaluateHOLFiniteState (callEntryStateHOLFinite state locals) foundBody with
        | mk result post =>
          rw [run] at globals
          change post.globals = state.globals at globals
          cases result with
          | none => exact globals
          | some result =>
            cases result <;> dsimp only
            all_goals (try split) <;> all_goals (try split) <;> all_goals
              (first
                | exact globals
                | (simp only [setKvarHOLFinite,setVarHOLFinite,emptyLocalsHOLFinite]; exact globals))

/-- A declaration call binding its result to a local retains globals when both the installed body
and the continuation do, in every outcome. -/
theorem originalGlobalsFrame_local_decCall (name : MlS) (shape : ShapeHOL) (function : MlS)
    (parameters : List (MlS × ShapeHOL)) (body : ProgHOL 64) (returnShape : ShapeHOL)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (bodyFrame : OriginalGlobalsFrame body) (continuation : ProgHOL 64)
    (contFrame : OriginalGlobalsFrame continuation) (arguments : List (ExpHOL 64)) :
    OriginalGlobalsFrame (.decCall name shape function arguments continuation) := by
  intro F state code
  rw [evaluateHOLFiniteState_decCall_total]
  dsimp only
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
        have same := lookupCodeHOLFinite_installed_body state.code.lookup function parameters body
          foundBody returnShape foundShape values locals (by rw [code]; exact installed) lookup
        have globals := bodyFrame (callEntryStateHOLFinite state locals) code
        rw [← same] at globals
        cases run : evaluateHOLFiniteState (callEntryStateHOLFinite state locals) foundBody with
        | mk result post =>
          rw [run] at globals
          change post.globals = state.globals at globals
          dsimp only
          cases result with
          | none => simpa only [fixClockHOLFinite] using globals
          | some result =>
            cases result with
            | returned value =>
              dsimp only
              split
              · dsimp only
                let ready : PanSemStateFiniteExact 64 F :=
                  {(fixClockHOLFinite (callEntryStateHOLFinite state locals)
                    (some (PanSemResultExact.returned value),post)).2 with locals := state.locals}
                have readyGlobals : ready.globals = state.globals := by
                  simp only [ready,fixClockHOLFinite]
                  exact globals
                have postCode : post.code = state.code := by
                  have met := (evaluateHOLFiniteState_metadata
                    (callEntryStateHOLFinite state locals) foundBody).1
                  rw [run] at met
                  exact met
                have readyCode : ready.code = originalRuntimeCode := by
                  simp only [ready,fixClockHOLFinite]
                  rw [postCode]
                  exact code
                have frame := contFrame (setVarHOLFinite name value ready) readyCode
                show (evaluateHOLFiniteState (setVarHOLFinite name value ready) continuation).2.globals
                  = state.globals
                exact frame.trans readyGlobals
              · simpa only [fixClockHOLFinite] using globals
            | error => simpa only [fixClockHOLFinite,emptyLocalsHOLFinite] using globals
            | timeOut => simpa only [fixClockHOLFinite,emptyLocalsHOLFinite] using globals
            | «break» => simpa only [fixClockHOLFinite,emptyLocalsHOLFinite] using globals
            | «continue» => simpa only [fixClockHOLFinite,emptyLocalsHOLFinite] using globals
            | exception id value => simpa only [fixClockHOLFinite,emptyLocalsHOLFinite] using globals
            | finalFfi event => simpa only [fixClockHOLFinite,emptyLocalsHOLFinite] using globals

#print axioms originalGlobalsFrame_tail_call
#print axioms originalGlobalsFrame_local_call
#print axioms originalGlobalsFrame_local_decCall
