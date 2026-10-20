import InitECandidate.Runtime.JournalGlobalKeep
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000000
set_option cbv.warning false
/-!
Whole-program instance of `GlobalKeep` for the block-output record pointer `bo` (assigned only in `execute_block`):
every original function outside `execute_block`, `input_blob` (shared-memory loads) and their callers keeps `bo`, at every fuel and in every outcome.
-/
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original functions that may change `bo` (directly or through callees). -/
def badBo : List MlS :=
  [ofString "attempt_l1",ofString "attempt_l2",ofString "attempt_l3",ofString "attempt_l4",ofString "attempt_l5",
    ofString "attempt_l6",ofString "attempt_l7",ofString "execute_block",ofString "input_blob",ofString "main",ofString "run_attempt",
    ofString "verify_stateless_new_payload"]

def goodBo (function : MlS) : Bool := !(badBo.contains function)

theorem program_check_bo : (functionsHOL sourceDeclarations).all
    (fun entry => !(goodBo entry.1) || keepsG (ofString "bo") goodBo entry.2.2.1) = true := by
  decide_cbv

theorem goodBo_bodies : ∀ function, goodBo function = true → ∀ values body callee rs,
    lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
    keepsG (ofString "bo") goodBo body = true := by
  intro f hf values body callee rs h
  obtain ⟨params,rs',hc⟩ := lookupCode_installed h
  have := List.all_eq_true.mp program_check_bo _ (originalRuntimeCode_mem hc)
  simpa [hf] using this

theorem keepsBo_of_installed {f : MlS} {params : List (MlS × ShapeHOL)} {body : ProgHOL 64} {rs : ShapeHOL}
    (h : originalRuntimeCode.lookup f = some (params,body,rs)) (hf : goodBo f = true) :
    keepsG (ofString "bo") goodBo body = true := by
  have := List.all_eq_true.mp program_check_bo _ (originalRuntimeCode_mem h)
  simpa [hf] using this

theorem evaluate_keeps_bo {F : Type} (program : ProgHOL 64)
    (supported : keepsG (ofString "bo") goodBo program = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state program).2.globals.lookup (ofString "bo") =
      state.globals.lookup (ofString "bo") :=
  evaluate_keepsG _ goodBo goodBo_bodies program supported state code

#print axioms program_check_bo
#print axioms evaluate_keeps_bo
end InitECandidate.Runtime
