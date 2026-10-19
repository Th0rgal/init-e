import InitECandidate.Runtime.JournalGlobalKeep
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000000
set_option cbv.warning false
/-!
Whole-program instance of `GlobalKeep` for the global `sk_buf` (assigned only in `state_init`, so changed only by the
initialisation drivers listed in `badJournalCap`): every original function outside that set keeps `sk_buf`, at every
fuel and in every outcome.
-/
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem program_check_sk_buf : (functionsHOL sourceDeclarations).all
    (fun entry => !(goodJournalCap entry.1) || keepsG (ofString "sk_buf") goodJournalCap entry.2.2.1) = true := by
  decide_cbv

theorem goodSkBuf_bodies : ∀ function, goodJournalCap function = true → ∀ values body callee rs,
    lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
    keepsG (ofString "sk_buf") goodJournalCap body = true := by
  intro f hf values body callee rs h
  obtain ⟨params,rs',hc⟩ := lookupCode_installed h
  have := List.all_eq_true.mp program_check_sk_buf _ (originalRuntimeCode_mem hc)
  simpa [hf] using this

theorem keepsSkBuf_of_installed {f : MlS} {params : List (MlS × ShapeHOL)} {body : ProgHOL 64} {rs : ShapeHOL}
    (h : originalRuntimeCode.lookup f = some (params,body,rs)) (hf : goodJournalCap f = true) :
    keepsG (ofString "sk_buf") goodJournalCap body = true := by
  have := List.all_eq_true.mp program_check_sk_buf _ (originalRuntimeCode_mem h)
  simpa [hf] using this

theorem evaluate_keeps_sk_buf {F : Type} (program : ProgHOL 64)
    (supported : keepsG (ofString "sk_buf") goodJournalCap program = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state program).2.globals.lookup (ofString "sk_buf") =
      state.globals.lookup (ofString "sk_buf") :=
  evaluate_keepsG _ goodJournalCap goodSkBuf_bodies program supported state code

#print axioms program_check_sk_buf
#print axioms evaluate_keeps_sk_buf
end InitECandidate.Runtime
