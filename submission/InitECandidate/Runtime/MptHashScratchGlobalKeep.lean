import InitECandidate.Runtime.EvGlobalKeep
import InitECandidate.Runtime.OriginalValidateHeadersCode
import InitECandidate.Runtime.RunAttemptHeadersSource
/-!
The original validating body keeps `mpt_hash_scratch` for every outcome.

`parserWorkspaceGlobals` covers `keccak_st`, `keccak_pad` and `mpt_nib_scratch`
but not `mpt_hash_scratch`, which the node-database builder needs from the
caller.  This module repeats the whole-program `keepsG` decision for that single
global: the only original function that assigns it is `mpt_init` (through a call
whose destination is the global itself), so excluding `mpt_init` from the good
set leaves a kernel-checked syntactic proof that every installed original body
outside that exclusion never assigns it and only calls functions that keep it.

No call frame is assumed: `evaluate_keepsG` turns the syntactic check into an
equality of the global's value at every fuel and every outcome, and the result is
instantiated at the whole actual `validate_headers` body.
-/
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000000
set_option cbv.warning false

/-- The node-database scratch workspace global watched by this module. -/
def mptHashScratchGlobals : List MlS := [ofString "mpt_hash_scratch"]

/-- Reuse the established conservative driver exclusions and additionally
exclude `mpt_init`, the only original function assigning `mpt_hash_scratch`. -/
def mptHashScratchGood (function : MlS) : Bool :=
  evGood function && !([ofString "mpt_init"].contains function)

/-- Kernel computation checks every installed original body; good calls remain
inside the checked set. -/
theorem mpt_hash_scratch_program_check : (functionsHOL sourceDeclarations).all
    (fun entry => !(mptHashScratchGood entry.1) || mptHashScratchGlobals.all
      (fun name => keepsG name mptHashScratchGood entry.2.2.1)) = true := by
  decide_cbv

theorem mpt_hash_scratch_installed {function : MlS} {parameters : List (MlS × ShapeHOL)}
    {body : ProgHOL 64} {shape : ShapeHOL}
    (installed : originalRuntimeCode.lookup function = some (parameters,body,shape))
    (good : mptHashScratchGood function = true) (name : MlS) (member : name ∈ mptHashScratchGlobals) :
    keepsG name mptHashScratchGood body = true := by
  have checked := List.all_eq_true.mp mpt_hash_scratch_program_check _ (originalRuntimeCode_mem installed)
  have allNames : mptHashScratchGlobals.all (fun name => keepsG name mptHashScratchGood body) = true := by
    simpa [good] using checked
  exact List.all_eq_true.mp allNames name member

theorem mpt_hash_scratch_good_bodies (name : MlS) (member : name ∈ mptHashScratchGlobals) :
    ∀ function, mptHashScratchGood function = true → ∀ values body callee shape,
      lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,shape) →
      keepsG name mptHashScratchGood body = true := by
  intro function good values body callee shape lookup
  obtain ⟨parameters,returnShape,installed⟩ := lookupCode_installed lookup
  exact mpt_hash_scratch_installed installed good name member

/-- Checked programs keep `mpt_hash_scratch` at every fuel and outcome. -/
theorem evaluate_keeps_mpt_hash_scratch {F : Type} (name : MlS)
    (member : name ∈ mptHashScratchGlobals) (program : ProgHOL 64)
    (supported : keepsG name mptHashScratchGood program = true)
    (s : PanSemStateFiniteExact 64 F) (code : s.code = originalRuntimeCode) :
    (evaluateHOLFiniteState s program).2.globals.lookup name = s.globals.lookup name :=
  evaluate_keepsG name mptHashScratchGood (mpt_hash_scratch_good_bodies name member) program
    supported s code

/-- The whole actual `validate_headers` body keeps `mpt_hash_scratch`: the
caller's workspace value survives every outcome of the validating call. -/
theorem validate_headers_keeps_mpt_hash_scratch {F : Type} (s : PanSemStateFiniteExact 64 F)
    (code : s.code = originalRuntimeCode) :
    (evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_validate_headers)).2.globals.lookup
        (ofString "mpt_hash_scratch") =
      s.globals.lookup (ofString "mpt_hash_scratch") :=
  evaluate_keeps_mpt_hash_scratch (ofString "mpt_hash_scratch") (by simp [mptHashScratchGlobals]) _
    (mpt_hash_scratch_installed originalRuntimeCode_validateHeaders_lookup (by decide) _
      (by simp [mptHashScratchGlobals]))
    s code

#print axioms mpt_hash_scratch_program_check
#print axioms mpt_hash_scratch_installed
#print axioms mpt_hash_scratch_good_bodies
#print axioms evaluate_keeps_mpt_hash_scratch
#print axioms validate_headers_keeps_mpt_hash_scratch
end InitECandidate.Runtime
