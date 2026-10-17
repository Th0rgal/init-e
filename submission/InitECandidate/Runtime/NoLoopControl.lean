import InitECandidate.Runtime.PanDecCallNoLoopControl
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

def noLoopControl : ProgHOL 64 → Bool
  | .dec _ _ _ body => noLoopControl body
  | .seq first second => noLoopControl first && noLoopControl second
  | .ite _ yes no => noLoopControl yes && noLoopControl no
  | .decCall _ _ _ _ continuation => noLoopControl continuation
  | .call (some (none,none)) _ _ => true
  | .skip | .annot _ _ | .assign _ _ _ | .raise _ _ | .return _ => true
  | _ => false

/-- Checked source fragments emit no break/continue, including when an opaque
callee attempts to do so. Calls and declaration scopes use their real semantics. -/
theorem evaluate_noLoopControl {F : Type} (program : ProgHOL 64)
    (supported : noLoopControl program = true) (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state program).1 ≠ some .break ∧
    (evaluateHOLFiniteState state program).1 ≠ some .continue := by
  cases shape : program with
  | skip => simp [evaluateHOLFiniteState_skip]
  | dec name kind initializer body =>
    have child : noLoopControl body = true := by simpa only [shape,noLoopControl] using supported
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · split
      · exact evaluate_noLoopControl body child _
      · simp
  | assign kind name value =>
    rw [evaluateHOLFiniteState_assign]
    split
    · simp
    · split <;> simp
  | seq first second =>
    have children : noLoopControl first = true ∧ noLoopControl second = true := by
      simpa only [shape,noLoopControl,Bool.and_eq_true] using supported
    have firstControl := evaluate_noLoopControl first children.1 state
    rw [evaluateHOLFiniteState_seq_line780]
    cases run : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [run] at firstControl
      cases result with
      | none => exact evaluate_noLoopControl second children.2 middle
      | some result => exact firstControl
  | ite condition yes no =>
    have children : noLoopControl yes = true ∧ noLoopControl no = true := by
      simpa only [shape,noLoopControl,Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noLoopControl no children.2 state
      · exact evaluate_noLoopControl yes children.1 state
    · simp
  | decCall name kind function arguments continuation =>
    have child : noLoopControl continuation = true := by simpa only [shape,noLoopControl] using supported
    exact evaluate_decCall_no_loop_control state name function kind arguments continuation
      (fun next => evaluate_noLoopControl continuation child next)
  | call info function arguments =>
    cases info with
    | none => simp [shape,noLoopControl] at supported
    | some data =>
      obtain ⟨target,handler⟩ := data
      cases target with
      | none =>
        cases handler with
        | none => exact evaluate_discard_call_no_loop_control state function arguments
        | some handler => simp [shape,noLoopControl] at supported
      | some target => simp [shape,noLoopControl] at supported
  | annot tag text => simp [evaluateHOLFiniteState_annot]
  | raise name value =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> simp
    · simp
  | «return» value =>
    rw [evaluateHOLFiniteState_return]
    split
    · simp
    · split <;> simp
  | _ => simp [shape,noLoopControl] at supported
termination_by sizeOf program
decreasing_by all_goals simp_all <;> omega

#print axioms evaluate_noLoopControl
end InitECandidate.Runtime
