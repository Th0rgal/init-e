import InitECandidate.Runtime.JournalGlobalKeep
/-!
The block-environment global `be` is assigned only by `run_attempt` (fork.pnk `be = alloc(BE_SIZE)`).  `BeKeep` is the
whole-program decidable check that every original function outside `run_attempt` and its callers keeps `be` (the same
shape as root's `program_check_journal`); it is stated as an explicit premise, to be closed by `decide_cbv` with
root's raised evaluation limits (as for `BalKeep2`).  From it, every good function keeps `be` at every fuel.
-/
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def badBe : List MlS :=
  [ofString "main", ofString "run_attempt", ofString "attempt_l1", ofString "attempt_l2", ofString "attempt_l3",
    ofString "attempt_l4", ofString "attempt_l5", ofString "attempt_l6", ofString "attempt_l7",
    ofString "verify_stateless_new_payload"]

def goodBe (function : MlS) : Bool := !(badBe.contains function)

/-- The decidable whole-program check (closed by `decide_cbv`). -/
def BeKeep : Prop := (functionsHOL sourceDeclarations).all
    (fun entry => !(goodBe entry.1) || keepsG (ofString "be") goodBe entry.2.2.1) = true

theorem goodBe_bodies (bk : BeKeep) : ∀ function, goodBe function = true → ∀ values body callee rs,
    lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
    keepsG (ofString "be") goodBe body = true := by
  intro f hf values body callee rs h
  obtain ⟨params,rs',hc⟩ := lookupCode_installed h
  have := List.all_eq_true.mp bk _ (originalRuntimeCode_mem hc)
  simpa [hf] using this

theorem evaluate_keeps_be (bk : BeKeep) {F : Type} (program : ProgHOL 64)
    (supported : keepsG (ofString "be") goodBe program = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state program).2.globals.lookup (ofString "be") =
      state.globals.lookup (ofString "be") :=
  evaluate_keepsG _ goodBe (goodBe_bodies bk) program supported state code

#print axioms goodBe_bodies
#print axioms evaluate_keeps_be
end InitECandidate.Runtime
