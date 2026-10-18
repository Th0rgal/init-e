import InitECandidate.Runtime.WhileTerminalControl
import InitECandidate.Runtime.PanHandlerFreeCallControl
import InitECandidate.Runtime.PanDecCallNoReturn
import InitECandidate.Runtime.TrapNoReturn
import InitECandidate.Runtime.StoreControlFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

def noDirectReturnWhile : ProgHOL 64 → Bool
  | .while _ body => noDirectReturnWhile body
  | .dec _ _ _ body => noDirectReturnWhile body
  | .seq first second => noDirectReturnWhile first && noDirectReturnWhile second
  | .ite _ yes no => noDirectReturnWhile yes && noDirectReturnWhile no
  | .decCall _ _ _ _ continuation => noDirectReturnWhile continuation
  | .call (some (_,none)) _ _ => true
  | .store _ _ => true
  | .skip | .break | .continue | .annot _ _ | .assign _ _ _ | .raise _ _ => true
  | _ => false

/-- Checked return-free source fragments cannot emit final returned values;
callee returns are consumed by their actual call or declaration semantics. -/
theorem evaluate_noDirectReturnWhile {F : Type} (program : ProgHOL 64)
    (supported : noDirectReturnWhile program = true) (state : PanSemStateFiniteExact 64 F) (value : ValueHOL 64) :
    (evaluateHOLFiniteState state program).1 ≠ some (.returned value) := by
  cases shape : program with
  | «while» condition body =>
    have child : noDirectReturnWhile body = true := by simpa only [shape,noDirectReturnWhile] using supported
    exact (evaluate_while_terminal_control condition body
      (fun current returned => evaluate_noDirectReturnWhile body child current returned) state).2.2 value
  | skip => simp [evaluateHOLFiniteState_skip]
  | dec name kind initializer body =>
    have child : noDirectReturnWhile body = true := by simpa only [shape,noDirectReturnWhile] using supported
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · split
      · exact evaluate_noDirectReturnWhile body child _ value
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
    have children : noDirectReturnWhile first = true ∧ noDirectReturnWhile second = true := by
      simpa only [shape,noDirectReturnWhile,Bool.and_eq_true] using supported
    exact evaluate_sequence_no_return state first second value (evaluate_noDirectReturnWhile first children.1 state value)
      (fun next => evaluate_noDirectReturnWhile second children.2 next value)
  | ite condition yes no =>
    have children : noDirectReturnWhile yes = true ∧ noDirectReturnWhile no = true := by
      simpa only [shape,noDirectReturnWhile,Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noDirectReturnWhile no children.2 state value
      · exact evaluate_noDirectReturnWhile yes children.1 state value
    · simp
  | decCall name kind function arguments continuation =>
    have child : noDirectReturnWhile continuation = true := by simpa only [shape,noDirectReturnWhile] using supported
    exact evaluate_decCall_no_return state name function kind arguments continuation
      (fun next returnedValue => evaluate_noDirectReturnWhile continuation child next returnedValue) value
  | call info function arguments =>
    cases info with
    | none => simp [shape,noDirectReturnWhile] at supported
    | some data =>
      obtain ⟨target,handler⟩ := data
      cases handler with
      | none => exact (evaluate_handlerFree_call_control state target function arguments).2.2 value
      | some handler => simp [shape,noDirectReturnWhile] at supported
  | annot tag text => simp [evaluateHOLFiniteState_annot]
  | raise name value =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> simp
    · simp
  | «break» => simp [evaluateHOLFiniteState_break]
  | «continue» => simp [evaluateHOLFiniteState_continue]
  | _ => simp [shape,noDirectReturnWhile] at supported
termination_by sizeOf program
decreasing_by all_goals simp_all <;> omega

#print axioms evaluate_noDirectReturnWhile
end InitECandidate.Runtime
