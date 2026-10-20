import InitECandidate.Runtime.JournalGlobalKeep
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000000
set_option cbv.warning false
/-!
Whole-program instance of `GlobalKeep` for the secp256k1 accelerator scratch pointer `secp_accel_scratch` (assigned only
in `secp256k1_init`): every original function outside `secp256k1_init`, its callers and the checker exceptions keeps it,
at every fuel and in every outcome.
-/
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original functions that may change `secp_accel_scratch` (directly or through callees), or that the checker rejects. -/
def badScr : List MlS :=
  [ofString "attempt_l1",ofString "attempt_l2",ofString "attempt_l3",ofString "attempt_l4",ofString "attempt_l5",ofString "attempt_l6",ofString "attempt_l7",ofString "depth0_prepare",ofString "ec_add_affine",ofString "ec_mul",ofString "ec_mul2",ofString "execute_block",ofString "frame_prologue",ofString "frame_start",ofString "generic_call",ofString "generic_create",ofString "input_blob",ofString "main",ofString "op_call",ofString "op_callcode",ofString "op_create",ofString "op_create2",ofString "op_delegatecall",ofString "op_dispatch",ofString "op_staticcall",ofString "pre_ecrecover",ofString "process_checked_system_transaction",ofString "process_create_message",ofString "process_general_purpose_requests",ofString "process_message",ofString "process_message_call",ofString "process_transaction",ofString "process_unchecked_system_transaction",ofString "recover_authority",ofString "recover_sender",ofString "recover_sender_with_chain_id",ofString "recover_transaction_public_key",ofString "run_attempt",ofString "run_frames",ofString "run_precompile",ofString "secp256k1_ecrecover",ofString "secp256k1_init",ofString "secp256k1_recover",ofString "set_delegation",ofString "start_child",ofString "verify_stateless_new_payload"]

def goodScr (function : MlS) : Bool := !(badScr.contains function)

theorem program_check_scr : (functionsHOL sourceDeclarations).all
    (fun entry => !(goodScr entry.1) || keepsG (ofString "secp_accel_scratch") goodScr entry.2.2.1) = true := by
  decide_cbv

theorem goodScr_bodies : ∀ function, goodScr function = true → ∀ values body callee rs,
    lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
    keepsG (ofString "secp_accel_scratch") goodScr body = true := by
  intro f hf values body callee rs h
  obtain ⟨params,rs',hc⟩ := lookupCode_installed h
  have := List.all_eq_true.mp program_check_scr _ (originalRuntimeCode_mem hc)
  simpa [hf] using this

theorem keepsScr_of_installed {f : MlS} {params : List (MlS × ShapeHOL)} {body : ProgHOL 64} {rs : ShapeHOL}
    (h : originalRuntimeCode.lookup f = some (params,body,rs)) (hf : goodScr f = true) :
    keepsG (ofString "secp_accel_scratch") goodScr body = true := by
  have := List.all_eq_true.mp program_check_scr _ (originalRuntimeCode_mem h)
  simpa [hf] using this

theorem evaluate_keeps_scr {F : Type} (program : ProgHOL 64)
    (supported : keepsG (ofString "secp_accel_scratch") goodScr program = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state program).2.globals.lookup (ofString "secp_accel_scratch") =
      state.globals.lookup (ofString "secp_accel_scratch") :=
  evaluate_keepsG _ goodScr goodScr_bodies program supported state code

#print axioms program_check_scr
#print axioms evaluate_keeps_scr
end InitECandidate.Runtime
