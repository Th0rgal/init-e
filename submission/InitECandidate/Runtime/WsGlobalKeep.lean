import InitECandidate.Runtime.JournalGlobalKeep
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000000
set_option cbv.warning false
/-!
Whole-program instance of `GlobalKeep` for the `u256_ws` workspace pointer (assigned only in `u256_ws_init`, called only
from `main`): every original function outside `u256_ws_init`, the `bo` exceptions and their callers keeps `u256_ws`, at
every fuel and in every outcome.
-/
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original functions that may change `u256_ws` (directly or through callees), or that the checker rejects. -/
def badWs : List MlS :=
  [ofString "attempt_l1",ofString "attempt_l2",ofString "attempt_l3",ofString "attempt_l4",ofString "attempt_l5",
    ofString "attempt_l6",ofString "attempt_l7",ofString "execute_block",ofString "input_blob",ofString "main",ofString "run_attempt",
    ofString "verify_stateless_new_payload",ofString "u256_ws_init"]

def goodWs (function : MlS) : Bool := !(badWs.contains function)

theorem program_check_ws : (functionsHOL sourceDeclarations).all
    (fun entry => !(goodWs entry.1) || keepsG (ofString "u256_ws") goodWs entry.2.2.1) = true := by
  decide_cbv

theorem goodWs_bodies : ∀ function, goodWs function = true → ∀ values body callee rs,
    lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
    keepsG (ofString "u256_ws") goodWs body = true := by
  intro f hf values body callee rs h
  obtain ⟨params,rs',hc⟩ := lookupCode_installed h
  have := List.all_eq_true.mp program_check_ws _ (originalRuntimeCode_mem hc)
  simpa [hf] using this

theorem keepsWs_of_installed {f : MlS} {params : List (MlS × ShapeHOL)} {body : ProgHOL 64} {rs : ShapeHOL}
    (h : originalRuntimeCode.lookup f = some (params,body,rs)) (hf : goodWs f = true) :
    keepsG (ofString "u256_ws") goodWs body = true := by
  have := List.all_eq_true.mp program_check_ws _ (originalRuntimeCode_mem h)
  simpa [hf] using this

theorem evaluate_keeps_ws {F : Type} (program : ProgHOL 64)
    (supported : keepsG (ofString "u256_ws") goodWs program = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state program).2.globals.lookup (ofString "u256_ws") =
      state.globals.lookup (ofString "u256_ws") :=
  evaluate_keepsG _ goodWs goodWs_bodies program supported state code

#print axioms program_check_ws
#print axioms evaluate_keeps_ws
end InitECandidate.Runtime
