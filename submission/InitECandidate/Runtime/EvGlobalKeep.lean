import InitECandidate.Runtime.GlobalKeep
import InitECandidate.Runtime.OriginalRuntimeCode
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 100000000000
set_option cbv.warning false
/-!
Whole-program instance of `GlobalKeep` for the frame-environment global `ev`: a kernel-checked decision over all
original declarations shows every function outside the 32 listed in `evBad` (the message/frame drivers and their
callers) keeps `ev` (`evaluate_keeps_ev`).
-/
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original functions that may change the frame-environment global `ev` (directly or through callees). -/
def evBad : List MlS :=
  [ofString "main",
    ofString "input_blob",
    ofString "op_dispatch",
    ofString "frame_open",
    ofString "finish_child",
    ofString "run_frames",
    ofString "start_child",
    ofString "process_message",
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

def evGood (function : MlS) : Bool := !(evBad.contains function)

/-- Whole-program check: every original function outside `evBad` passes the `ev`-keeping syntactic check. -/
theorem ev_program_check : (functionsHOL sourceDeclarations).all
    (fun entry => !(evGood entry.1) || keepsG (ofString "ev") evGood entry.2.2.1) = true := by
  decide_cbv

#print axioms ev_program_check

theorem lookupCode_installed {code : MlS → Option (List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL)} {f : MlS}
    {values : List (ValueHOL 64)} {body : ProgHOL 64} {callee : HolFiniteMapExact MlS (ValueHOL 64)} {rs : ShapeHOL}
    (h : PanSemStateFiniteExact.lookupCodeHOLFinite code f values = some (body,callee,rs)) :
    ∃ params rs', code f = some (params,body,rs') := by
  unfold PanSemStateFiniteExact.lookupCodeHOLFinite at h
  split at h
  · cases h
  · rename_i fb fl fs found
    simp only [Option.some.injEq,Prod.mk.injEq] at h
    obtain ⟨rfl,_,_⟩ := h
    unfold lookupCodeHOLExact at found
    split at found
    · cases found
    · rename_i params b r hc
      split at found
      · simp only [Option.some.injEq,Prod.mk.injEq] at found
        obtain ⟨rfl,_,_⟩ := found
        exact ⟨params,r,hc⟩
      · cases found

theorem list_lookup_mem {α β : Type} [BEq α] [LawfulBEq α] {a : α} {b : β} :
    ∀ {l : List (α × β)}, List.lookup a l = some b → (a,b) ∈ l
  | [], h => by simp at h
  | (k,v) :: t, h => by
    by_cases e : a = k
    · subst e; simp [List.lookup] at h; subst h; simp
    · have : (a == k) = false := by simpa using e
      simp [List.lookup,this] at h
      exact List.mem_cons_of_mem _ (list_lookup_mem h)

theorem originalRuntimeCode_mem {f : MlS} {x : List (MlS × ShapeHOL) × ProgHOL 64 × ShapeHOL}
    (h : originalRuntimeCode.lookup f = some x) : (f,x) ∈ functionsHOL sourceDeclarations := by
  have e : originalRuntimeCode.lookup f = List.lookup f (functionsHOL sourceDeclarations).reverse := by
    change (HolFiniteMapExact.empty.updateList (functionsHOL sourceDeclarations)).lookup _ = _
    rw [HolFiniteMapExact.lookup_updateList]
    change FUPDATE_LIST FEMPTY (functionsHOL sourceDeclarations) f = _
    simpa only [List.reverse_reverse,FLOOKUP] using
      FLOOKUP_FUPDATE_LIST_reverse_eq_lookup (functionsHOL sourceDeclarations).reverse f
  rw [e] at h
  exact List.mem_reverse.mp (list_lookup_mem h)

/-- Every installed body of an `ev`-good function passes the `ev`-keeping check. -/
theorem evGood_bodies : ∀ function, evGood function = true → ∀ values body callee rs,
    lookupCodeHOLFinite originalRuntimeCode.lookup function values = some (body,callee,rs) →
    keepsG (ofString "ev") evGood body = true := by
  intro f hf values body callee rs h
  obtain ⟨params,rs',hc⟩ := lookupCode_installed h
  have mem := originalRuntimeCode_mem hc
  have := List.all_eq_true.mp ev_program_check _ mem
  simpa [hf] using this

/-- The frame-environment global `ev` is unchanged by every original function outside `evBad`, at every fuel and in
every outcome. -/
theorem evaluate_keeps_ev {F : Type} (program : ProgHOL 64) (supported : keepsG (ofString "ev") evGood program = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state program).2.globals.lookup (ofString "ev") = state.globals.lookup (ofString "ev") :=
  evaluate_keepsG _ evGood evGood_bodies program supported state code

#print axioms evGood_bodies
#print axioms evaluate_keeps_ev
end InitECandidate.Runtime
