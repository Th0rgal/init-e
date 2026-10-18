import InitECandidate.Runtime.WhileNoLoopControl
import InitECandidate.Runtime.NoDirectReturn
import InitECandidate.Runtime.PanHandlerFreeCallControl
import InitECandidate.Runtime.PanDecCallNoLoopControl
import InitECandidate.Runtime.StoreControlFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

def noLoopControlWhile : ProgHOL 64 → Bool
  | .dec _ _ _ body => noLoopControlWhile body
  | .seq first second => noLoopControlWhile first && noLoopControlWhile second
  | .ite _ yes no => noLoopControlWhile yes && noLoopControlWhile no
  | .decCall _ _ _ _ continuation => noLoopControlWhile continuation
  | .call (some (_,none)) _ _ => true
  | .while _ _ => true
  | .store _ _ => true
  | .skip | .annot _ _ | .assign _ _ _ | .raise _ _ | .return _ => true
  | _ => false

/-- Checked source fragments emit no break/continue, including when an opaque
callee attempts to do so. Calls and declaration scopes use their real semantics. -/
theorem evaluate_noLoopControlWhile {F : Type} (program : ProgHOL 64)
    (supported : noLoopControlWhile program = true) (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state program).1 ≠ some .break ∧
    (evaluateHOLFiniteState state program).1 ≠ some .continue := by
  cases shape : program with
  | skip => simp [evaluateHOLFiniteState_skip]
  | dec name kind initializer body =>
    have child : noLoopControlWhile body = true := by simpa only [shape,noLoopControlWhile] using supported
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · split
      · exact evaluate_noLoopControlWhile body child _
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
    have children : noLoopControlWhile first = true ∧ noLoopControlWhile second = true := by
      simpa only [shape,noLoopControlWhile,Bool.and_eq_true] using supported
    have firstControl := evaluate_noLoopControlWhile first children.1 state
    rw [evaluateHOLFiniteState_seq_line780]
    cases run : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [run] at firstControl
      cases result with
      | none => exact evaluate_noLoopControlWhile second children.2 middle
      | some result => exact firstControl
  | ite condition yes no =>
    have children : noLoopControlWhile yes = true ∧ noLoopControlWhile no = true := by
      simpa only [shape,noLoopControlWhile,Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noLoopControlWhile no children.2 state
      · exact evaluate_noLoopControlWhile yes children.1 state
    · simp
  | decCall name kind function arguments continuation =>
    have child : noLoopControlWhile continuation = true := by simpa only [shape,noLoopControlWhile] using supported
    exact evaluate_decCall_no_loop_control state name function kind arguments continuation
      (fun next => evaluate_noLoopControlWhile continuation child next)
  | call info function arguments =>
    cases info with
    | none => simp [shape,noLoopControlWhile] at supported
    | some data =>
      obtain ⟨target,handler⟩ := data
      cases handler with
      | none =>
        have control := evaluate_handlerFree_call_control state target function arguments
        exact ⟨control.1,control.2.1⟩
      | some handler => simp [shape,noLoopControlWhile] at supported
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
  | «while» condition body => exact evaluate_while_no_loop_control condition body state
  | _ => simp [shape,noLoopControlWhile] at supported
termination_by sizeOf program
decreasing_by all_goals simp_all <;> omega

#print axioms evaluate_noLoopControlWhile
end InitECandidate.Runtime
