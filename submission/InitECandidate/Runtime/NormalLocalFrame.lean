import InitECandidate.Runtime.StraightLocalFrame
import InitECandidate.Runtime.PanDecNormalScope
import InitECandidate.Runtime.PanDecCallUnconditionalNormalScope
import InitECandidate.Runtime.LocalCallSuccessOtherLocals
import InitECandidate.Runtime.PanSequenceTerminal
import InitECandidate.Runtime.TrapBodyClock
import InitECandidate.Runtime.StoreControlFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Caller-local preservation on normal paths, with callees opaque and all
exceptional paths excluded by the actual evaluator result. -/
def normalLocalFrameSyntax (key : MlS) : ProgHOL 64 → Bool
  | .dec name _ _ body | .decCall name _ _ _ body => (name == key) || normalLocalFrameSyntax key body
  | .seq first second => normalLocalFrameSyntax key first && normalLocalFrameSyntax key second
  | .ite _ yes no => normalLocalFrameSyntax key yes && normalLocalFrameSyntax key no
  | .assign .local name _ => !(name == key)
  | .call (some (some (.local,name),none)) _ _ => !(name == key)
  | .store _ _ | .skip | .annot _ _ | .raise _ _ | .return _ => true
  | _ => false

theorem evaluate_normalLocalFrame {F : Type} (key : MlS) (program : ProgHOL 64)
    (supported : normalLocalFrameSyntax key program = true) (state post : PanSemStateFiniteExact 64 F)
    (run : evaluateHOLFiniteState state program = (none,post)) :
    post.locals.lookup key = state.locals.lookup key := by
  cases shape : program with
  | dec name kind initializer body =>
    rw [shape] at run
    obtain ⟨value,output,_,bodyRun,scope⟩ := evaluate_dec_normal_scope state post name kind initializer body run
    rw [scope]
    by_cases same : name = key
    · subst name
      cases saved : state.locals.lookup key <;>
        simp [HolFiniteMapExact.resVarEq,HolFiniteMapExact.lookup_updateEq,
          HolFiniteMapExact.lookup_eraseEq,FUPDATE_HOL,FDOMSUB_HOL]
    · have child : normalLocalFrameSyntax key body = true := by
        simpa [shape,normalLocalFrameSyntax,same] using supported
      rw [restore_other_local _ name key _ (Ne.symm same)]
      have kept := evaluate_normalLocalFrame key body child (setVarHOLFinite name value state) output bodyRun
      simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,same,Ne.symm same] using kept
  | decCall name kind function arguments body =>
    rw [shape] at run
    obtain ⟨value,ready,output,locals,bodyRun,scope⟩ :=
      evaluate_decCall_unconditional_normal_scope state post name function kind arguments body run
    rw [scope]
    by_cases same : name = key
    · subst name
      cases saved : state.locals.lookup key <;>
        simp [HolFiniteMapExact.resVarEq,HolFiniteMapExact.lookup_updateEq,
          HolFiniteMapExact.lookup_eraseEq,FUPDATE_HOL,FDOMSUB_HOL]
    · have child : normalLocalFrameSyntax key body = true := by
        simpa [shape,normalLocalFrameSyntax,same] using supported
      rw [restore_other_local _ name key _ (Ne.symm same)]
      have kept := evaluate_normalLocalFrame key body child (setVarHOLFinite name value ready) output bodyRun
      simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,same,Ne.symm same,locals] using kept
  | seq first second =>
    rw [shape] at run
    have children : normalLocalFrameSyntax key first = true ∧ normalLocalFrameSyntax key second = true := by
      simpa only [shape,normalLocalFrameSyntax,Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_seq_line780] at run
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at run
      cases result with
      | none =>
        exact (evaluate_normalLocalFrame key second children.2 middle post run).trans
          (evaluate_normalLocalFrame key first children.1 state middle firstRun)
      | some result => cases run
  | ite condition yes no =>
    rw [shape] at run
    have children : normalLocalFrameSyntax key yes = true ∧ normalLocalFrameSyntax key no = true := by
      simpa only [shape,normalLocalFrameSyntax,Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite] at run
    split at run
    · split at run
      · exact evaluate_normalLocalFrame key no children.2 state post run
      · exact evaluate_normalLocalFrame key yes children.1 state post run
    · cases run
  | assign kind name value =>
    rw [shape] at run
    cases kind with
    | global => simp [shape,normalLocalFrameSyntax] at supported
    | «local» =>
      have straight : straightLocalFrame key (.assign .local name value) = true := by
        simpa only [shape,normalLocalFrameSyntax,straightLocalFrame] using supported
      have kept := evaluate_straight_local_frame key (.assign .local name value) straight state
      rw [run] at kept
      exact kept
  | store destination value =>
    rw [shape] at run
    have kept := (evaluate_store_control_frame state destination value).2.1
    rw [run] at kept
    exact congrArg (fun locals => locals.lookup key) kept
  | call destination function arguments =>
    rw [shape] at run
    cases destination with
    | none => simp [shape,normalLocalFrameSyntax] at supported
    | some destination =>
      obtain ⟨destination,handler⟩ := destination
      cases handler with
      | some handler => simp [shape,normalLocalFrameSyntax] at supported
      | none =>
        cases destination with
        | none => simp [shape,normalLocalFrameSyntax] at supported
        | some destination =>
          obtain ⟨kind,name⟩ := destination
          cases kind with
          | global => simp [shape,normalLocalFrameSyntax] at supported
          | «local» =>
            have different : name ≠ key := by simpa [shape,normalLocalFrameSyntax] using supported
            have success : (evaluateHOLFiniteState state (.call (some (some (.local,name),none)) function arguments)).1 = none := by rw [run]
            have kept := evaluate_local_call_success_other_locals state function name arguments success key (Ne.symm different)
            rw [run] at kept
            exact kept
  | skip =>
    rw [shape] at run
    rw [evaluateHOLFiniteState_skip] at run
    have same := (Prod.mk.inj run).2
    simpa only [same] using (Eq.refl (state.locals.lookup key))
  | annot tag text =>
    rw [shape] at run
    rw [evaluateHOLFiniteState_annot] at run
    have same := (Prod.mk.inj run).2
    simpa only [same] using (Eq.refl (state.locals.lookup key))
  | raise name value =>
    rw [shape] at run
    have terminal := evaluate_raise_terminal state name value
    rw [run] at terminal
    exact False.elim (terminal rfl)
  | «return» value =>
    rw [shape] at run
    have terminal := evaluate_return_terminal state value
    rw [run] at terminal
    exact False.elim (terminal rfl)
  | _ => simp [shape,normalLocalFrameSyntax] at supported
termination_by sizeOf program

#print axioms evaluate_normalLocalFrame
end InitECandidate.Runtime
