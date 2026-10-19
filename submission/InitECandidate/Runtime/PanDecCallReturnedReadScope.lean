import InitECandidate.Runtime.PanDecCallReturnedBodyScope
import InitECandidate.Runtime.MemKeepProgram
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Invert an actual returned declaration-call to an installed memory-preserving
body. The continuation sees caller locals and the original memory observations. -/
theorem evaluate_decCall_returned_read_scope {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (name function : MlS)
    (shape returnShape : ShapeHOL) (arguments : List (ExpHOL 64))
    (parameters : List (MlS × ShapeHOL)) (body continuation : ProgHOL 64) (finalValue : ValueHOL 64)
    (code : s.code = originalRuntimeCode)
    (installed : originalRuntimeCode.lookup function = some (parameters,body,returnShape))
    (supported : keepsM goodMem body = true)
    (run : evaluateHOLFiniteState s (.decCall name shape function arguments continuation) =
      (some (.returned finalValue),post)) :
    ∃ (value : ValueHOL 64) (ready output : PanSemStateFiniteExact 64 F),
      ready.locals = s.locals ∧ ready.memory = s.memory ∧ ready.memaddrs = s.memaddrs ∧
      ready.be = s.be ∧ ready.code = s.code ∧
      evaluateHOLFiniteState (setVarHOLFinite name value ready) continuation =
        (some (.returned finalValue),output) := by
  cases args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) arguments with
  | none => rw [evaluateHOLFiniteState_decCall_total,args] at run; cases run
  | some values =>
    cases lookup : lookupCodeHOLFinite s.code.lookup function values with
    | none => rw [evaluateHOLFiniteState_decCall_total,args] at run; simp [lookup] at run
    | some found =>
      obtain ⟨actual,callee,actualShape⟩ := found
      have same := lookupCodeHOLFinite_installed_body s.code.lookup function parameters body actual returnShape
        actualShape values callee (by rw [code]; exact installed) lookup
      subst same
      obtain ⟨value,bodyPost,ready,output,bodyRun,locals,memory,domain,endian,readyCode,tail,_⟩ :=
        evaluate_decCall_returned_body_scope s post name function shape actualShape arguments values actual continuation
          callee finalValue args lookup run
      have frame := evaluate_keeps_mem actual supported (callEntryStateHOLFinite s callee) code
      have metadata := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite s callee) actual
      rw [bodyRun] at frame metadata
      exact ⟨value,ready,output,locals,memory.trans frame,domain.trans metadata.2.1,
        endian.trans metadata.2.2.1,readyCode.trans metadata.1,tail⟩

#print axioms evaluate_decCall_returned_read_scope
end InitECandidate.Runtime
