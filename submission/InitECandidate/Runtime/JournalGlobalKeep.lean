import InitECandidate.Runtime.EvGlobalKeep
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000000
set_option cbv.warning false
/-!
Whole-program instances of `GlobalKeep` for the journal globals `journal`, `journal_cap` (changed only by the
initialisation drivers) and `journal_n` (changed by the state writers and their callers): every original function
outside the listed sets keeps the respective global, at every fuel and in every outcome.
-/
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original functions that may change `journal` (directly or through callees). -/
def badJournal : List MlS :=
  [ofString "main",
    ofString "input_blob",
    ofString "state_init",
    ofString "run_attempt",
    ofString "attempt_l1",
    ofString "attempt_l2",
    ofString "attempt_l3",
    ofString "attempt_l4",
    ofString "attempt_l5",
    ofString "attempt_l6",
    ofString "attempt_l7",
    ofString "verify_stateless_new_payload"]

def goodJournal (function : MlS) : Bool := !(badJournal.contains function)

theorem program_check_journal : (functionsHOL sourceDeclarations).all
    (fun entry => !(goodJournal entry.1) || keepsG (ofString "journal") goodJournal entry.2.2.1) = true := by
  decide_cbv

theorem goodJournal_bodies : ∀ function, goodJournal function = true → ∀ values body callee rs,
    lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
    keepsG (ofString "journal") goodJournal body = true := by
  intro f hf values body callee rs h
  obtain ⟨params,rs',hc⟩ := lookupCode_installed h
  have := List.all_eq_true.mp program_check_journal _ (originalRuntimeCode_mem hc)
  simpa [hf] using this

theorem keepsJournal_of_installed {f : MlS} {params : List (MlS × ShapeHOL)} {body : ProgHOL 64} {rs : ShapeHOL}
    (h : originalRuntimeCode.lookup f = some (params,body,rs)) (hf : goodJournal f = true) :
    keepsG (ofString "journal") goodJournal body = true := by
  have := List.all_eq_true.mp program_check_journal _ (originalRuntimeCode_mem h)
  simpa [hf] using this

theorem evaluate_keeps_journal {F : Type} (program : ProgHOL 64)
    (supported : keepsG (ofString "journal") goodJournal program = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state program).2.globals.lookup (ofString "journal") =
      state.globals.lookup (ofString "journal") :=
  evaluate_keepsG _ goodJournal goodJournal_bodies program supported state code

/-- The original functions that may change `journal_cap` (directly or through callees). -/
def badJournalCap : List MlS :=
  [ofString "main",
    ofString "input_blob",
    ofString "state_init",
    ofString "run_attempt",
    ofString "attempt_l1",
    ofString "attempt_l2",
    ofString "attempt_l3",
    ofString "attempt_l4",
    ofString "attempt_l5",
    ofString "attempt_l6",
    ofString "attempt_l7",
    ofString "verify_stateless_new_payload"]

def goodJournalCap (function : MlS) : Bool := !(badJournalCap.contains function)

theorem program_check_journal_cap : (functionsHOL sourceDeclarations).all
    (fun entry => !(goodJournalCap entry.1) || keepsG (ofString "journal_cap") goodJournalCap entry.2.2.1) = true := by
  decide_cbv

theorem goodJournalCap_bodies : ∀ function, goodJournalCap function = true → ∀ values body callee rs,
    lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
    keepsG (ofString "journal_cap") goodJournalCap body = true := by
  intro f hf values body callee rs h
  obtain ⟨params,rs',hc⟩ := lookupCode_installed h
  have := List.all_eq_true.mp program_check_journal_cap _ (originalRuntimeCode_mem hc)
  simpa [hf] using this

theorem keepsJournalCap_of_installed {f : MlS} {params : List (MlS × ShapeHOL)} {body : ProgHOL 64} {rs : ShapeHOL}
    (h : originalRuntimeCode.lookup f = some (params,body,rs)) (hf : goodJournalCap f = true) :
    keepsG (ofString "journal_cap") goodJournalCap body = true := by
  have := List.all_eq_true.mp program_check_journal_cap _ (originalRuntimeCode_mem h)
  simpa [hf] using this

theorem evaluate_keeps_journal_cap {F : Type} (program : ProgHOL 64)
    (supported : keepsG (ofString "journal_cap") goodJournalCap program = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state program).2.globals.lookup (ofString "journal_cap") =
      state.globals.lookup (ofString "journal_cap") :=
  evaluate_keepsG _ goodJournalCap goodJournalCap_bodies program supported state code

/-- The original functions that may change `journal_n` (directly or through callees). -/
def badJournalN : List MlS :=
  [ofString "main",
    ofString "input_blob",
    ofString "state_init",
    ofString "state_fresh_tx",
    ofString "jset",
    ofString "jdel",
    ofString "state_restore",
    ofString "set_account",
    ofString "set_storage",
    ofString "destroy_storage",
    ofString "destroy_account",
    ofString "modify_state_commit",
    ofString "clear_account_preserving_balance",
    ofString "set_transient_storage",
    ofString "move_ether",
    ofString "create_ether",
    ofString "set_account_balance",
    ofString "increment_nonce",
    ofString "set_code",
    ofString "op_sstore",
    ofString "op_tstore",
    ofString "op_selfdestruct",
    ofString "set_delegation",
    ofString "op_dispatch",
    ofString "frame_prologue",
    ofString "frame_start",
    ofString "frame_epilogue",
    ofString "finish_child",
    ofString "run_frames",
    ofString "start_child",
    ofString "depth0_prepare",
    ofString "process_message",
    ofString "create_finish",
    ofString "process_create_message",
    ofString "generic_create",
    ofString "op_create",
    ofString "op_create2",
    ofString "generic_call",
    ofString "op_call",
    ofString "op_callcode",
    ofString "op_delegatecall",
    ofString "op_staticcall",
    ofString "process_message_call",
    ofString "process_unchecked_system_transaction",
    ofString "process_checked_system_transaction",
    ofString "process_transaction",
    ofString "process_withdrawals",
    ofString "process_general_purpose_requests",
    ofString "execute_block",
    ofString "run_attempt",
    ofString "attempt_l1",
    ofString "attempt_l2",
    ofString "attempt_l3",
    ofString "attempt_l4",
    ofString "attempt_l5",
    ofString "attempt_l6",
    ofString "attempt_l7",
    ofString "verify_stateless_new_payload"]

def goodJournalN (function : MlS) : Bool := !(badJournalN.contains function)

theorem program_check_journal_n : (functionsHOL sourceDeclarations).all
    (fun entry => !(goodJournalN entry.1) || keepsG (ofString "journal_n") goodJournalN entry.2.2.1) = true := by
  decide_cbv

theorem goodJournalN_bodies : ∀ function, goodJournalN function = true → ∀ values body callee rs,
    lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
    keepsG (ofString "journal_n") goodJournalN body = true := by
  intro f hf values body callee rs h
  obtain ⟨params,rs',hc⟩ := lookupCode_installed h
  have := List.all_eq_true.mp program_check_journal_n _ (originalRuntimeCode_mem hc)
  simpa [hf] using this

theorem keepsJournalN_of_installed {f : MlS} {params : List (MlS × ShapeHOL)} {body : ProgHOL 64} {rs : ShapeHOL}
    (h : originalRuntimeCode.lookup f = some (params,body,rs)) (hf : goodJournalN f = true) :
    keepsG (ofString "journal_n") goodJournalN body = true := by
  have := List.all_eq_true.mp program_check_journal_n _ (originalRuntimeCode_mem h)
  simpa [hf] using this

theorem evaluate_keeps_journal_n {F : Type} (program : ProgHOL 64)
    (supported : keepsG (ofString "journal_n") goodJournalN program = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state program).2.globals.lookup (ofString "journal_n") =
      state.globals.lookup (ofString "journal_n") :=
  evaluate_keepsG _ goodJournalN goodJournalN_bodies program supported state code

#print axioms program_check_journal
#print axioms evaluate_keeps_journal
#print axioms program_check_journal_cap
#print axioms evaluate_keeps_journal_cap
#print axioms program_check_journal_n
#print axioms evaluate_keeps_journal_n
end InitECandidate.Runtime
