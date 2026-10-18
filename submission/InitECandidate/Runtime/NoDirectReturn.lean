import InitECandidate.Runtime.PanHandlerFreeCallControl
import InitECandidate.Runtime.PanDecCallNoReturn
import InitECandidate.Runtime.TrapNoReturn
import InitECandidate.Runtime.StoreControlFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

def noDirectReturn : ProgHOL 64 → Bool
  | .dec _ _ _ body => noDirectReturn body
  | .seq first second => noDirectReturn first && noDirectReturn second
  | .ite _ yes no => noDirectReturn yes && noDirectReturn no
  | .decCall _ _ _ _ continuation => noDirectReturn continuation
  | .call (some (_,none)) _ _ => true
  | .store _ _ => true
  | .skip | .break | .continue | .annot _ _ | .assign _ _ _ | .raise _ _ => true
  | _ => false

/-- Checked return-free source fragments cannot emit final returned values;
callee returns are consumed by their actual call or declaration semantics. -/
theorem evaluate_noDirectReturn {F : Type} (program : ProgHOL 64)
    (supported : noDirectReturn program = true) (state : PanSemStateFiniteExact 64 F) (value : ValueHOL 64) :
    (evaluateHOLFiniteState state program).1 ≠ some (.returned value) := by
  cases shape : program with
  | skip => simp [evaluateHOLFiniteState_skip]
  | dec name kind initializer body =>
    have child : noDirectReturn body = true := by simpa only [shape,noDirectReturn] using supported
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · split
      · exact evaluate_noDirectReturn body child _ value
      · simp
  | assign kind name value =>
    rw [evaluateHOLFiniteState_assign]
    split
    · simp
    · split <;> simp
  | store destination value =>
    rcases (evaluate_store_control_frame state destination value).1 with normal | error
    · rw [normal]; simp
    · rw [error]; simp
  | seq first second =>
    have children : noDirectReturn first = true ∧ noDirectReturn second = true := by
      simpa only [shape,noDirectReturn,Bool.and_eq_true] using supported
    exact evaluate_sequence_no_return state first second value (evaluate_noDirectReturn first children.1 state value)
      (fun next => evaluate_noDirectReturn second children.2 next value)
  | ite condition yes no =>
    have children : noDirectReturn yes = true ∧ noDirectReturn no = true := by
      simpa only [shape,noDirectReturn,Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noDirectReturn no children.2 state value
      · exact evaluate_noDirectReturn yes children.1 state value
    · simp
  | decCall name kind function arguments continuation =>
    have child : noDirectReturn continuation = true := by simpa only [shape,noDirectReturn] using supported
    exact evaluate_decCall_no_return state name function kind arguments continuation
      (fun next returnedValue => evaluate_noDirectReturn continuation child next returnedValue) value
  | call info function arguments =>
    cases info with
    | none => simp [shape,noDirectReturn] at supported
    | some data =>
      obtain ⟨target,handler⟩ := data
      cases handler with
      | none => exact (evaluate_handlerFree_call_control state target function arguments).2.2 value
      | some handler => simp [shape,noDirectReturn] at supported
  | annot tag text => simp [evaluateHOLFiniteState_annot]
  | raise name value =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> simp
    · simp
  | «break» => simp [evaluateHOLFiniteState_break]
  | «continue» => simp [evaluateHOLFiniteState_continue]
  | _ => simp [shape,noDirectReturn] at supported
termination_by sizeOf program
decreasing_by all_goals simp_all <;> omega

#print axioms evaluate_noDirectReturn
end InitECandidate.Runtime
