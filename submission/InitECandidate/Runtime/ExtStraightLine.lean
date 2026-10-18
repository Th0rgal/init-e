import InitECandidate.Runtime.StraightLineNoTimeout
import InitECandidate.Runtime.ByteStoresControlFrame
import InitECandidate.Runtime.ByteStraightLine
import InitECandidate.Runtime.TrapPrimitiveClock
import InitECandidate.Runtime.TrapNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Straight-line source fragments including byte writes, primitives and external calls. -/
def extStraightLine {width : Nat} [NeZero width] : ProgHOL width → Bool
  | .dec _ _ _ body => extStraightLine body
  | .seq first second => extStraightLine first && extStraightLine second
  | .ite _ yes no => extStraightLine yes && extStraightLine no
  | .skip | .break | .continue | .annot _ _ => true
  | .assign _ _ _ | .storeByte _ _ | .store _ _ | .raise _ _ | .return _ => true
  | .primitive _ _ _ | .extCall _ _ _ _ _ => true
  | _ => false


theorem clockPreserving_of_extStraightLine {F : Type} (program : ProgHOL 64)
    (supported : extStraightLine program = true) : ClockPreserving (σ := F) program := by
  cases hprogram : program with
  | skip => exact clockPreserving_skip
  | dec name shape initializer body =>
    exact clockPreserving_dec name shape initializer body
      (clockPreserving_of_extStraightLine body (by simpa [hprogram, extStraightLine] using supported))
  | assign kind name value => exact clockPreserving_assign kind name value
  | storeByte destination value =>
    intro state
    exact (evaluate_storeByte_control_frame state destination value).2.1
  | store destination value => exact clockPreserving_store destination value
  | seq first second =>
    have pieces : extStraightLine first = true ∧ extStraightLine second = true := by
      simpa only [hprogram, extStraightLine, Bool.and_eq_true] using supported
    exact clockPreserving_seq first second (clockPreserving_of_extStraightLine first pieces.1)
      (clockPreserving_of_extStraightLine second pieces.2)
  | ite condition yes no =>
    have pieces : extStraightLine yes = true ∧ extStraightLine no = true := by
      simpa only [hprogram, extStraightLine, Bool.and_eq_true] using supported
    exact clockPreserving_ite condition yes no (clockPreserving_of_extStraightLine yes pieces.1)
      (clockPreserving_of_extStraightLine no pieces.2)
  | «break» => intro state; rw [evaluateHOLFiniteState_break]
  | «continue» => intro state; rw [evaluateHOLFiniteState_continue]
  | annot tag text => intro state; rw [evaluateHOLFiniteState_annot]
  | raise name value => exact clockPreserving_raise name value
  | «return» value => exact clockPreserving_return value
  | primitive name operator arguments =>
    intro state
    rw [evaluateHOLFiniteState_primitive]
    repeat' first | split | rfl
  | extCall function a b c d => intro state; exact evaluate_external_call_clock state function a b c d
  | _ => simp [hprogram, extStraightLine] at supported
termination_by sizeOf program
decreasing_by all_goals simp_all <;> omega


theorem evaluate_extStraightLine_no_timeout {F : Type} (program : ProgHOL 64)
    (supported : extStraightLine program = true) (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state program).1 ≠ some .timeOut := by
  cases shape : program with
  | skip => simp [evaluateHOLFiniteState_skip]
  | dec name kind initializer body =>
    have child : extStraightLine body = true := by simpa only [shape,extStraightLine] using supported
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · split
      · exact evaluate_extStraightLine_no_timeout body child _
      · simp
  | assign kind name value =>
    rw [evaluateHOLFiniteState_assign]
    split
    · simp
    · split <;> simp
  | storeByte destination value =>
    rcases (evaluate_storeByte_control_frame state destination value).1 with normal | error
    · rw [normal]; simp
    · rw [error]; simp
  | store destination value =>
    rcases (evaluate_store_control_frame state destination value).1 with normal | error
    · rw [normal]; simp
    · rw [error]; simp
  | seq first second =>
    have children : extStraightLine first = true ∧ extStraightLine second = true := by
      simpa only [shape,extStraightLine,Bool.and_eq_true] using supported
    exact evaluate_sequence_no_timeout state first second (evaluate_extStraightLine_no_timeout first children.1 state)
      (fun next => evaluate_extStraightLine_no_timeout second children.2 next)
  | ite condition yes no =>
    have children : extStraightLine yes = true ∧ extStraightLine no = true := by
      simpa only [shape,extStraightLine,Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_extStraightLine_no_timeout no children.2 state
      · exact evaluate_extStraightLine_no_timeout yes children.1 state
    · simp
  | «break» => simp [evaluateHOLFiniteState_break]
  | «continue» => simp [evaluateHOLFiniteState_continue]
  | annot tag text => simp [evaluateHOLFiniteState_annot]
  | raise name value => exact evaluate_raise_no_timeout state name value
  | «return» value =>
    rw [evaluateHOLFiniteState_return]
    split
    · simp
    · split <;> simp
  | primitive name operator arguments =>
    rw [evaluateHOLFiniteState_primitive]
    repeat' first | split | simp
  | extCall function a b c d => exact evaluate_external_call_no_timeout state function a b c d
  | _ => simp [shape,extStraightLine] at supported
termination_by sizeOf program
decreasing_by all_goals simp_all <;> omega


#print axioms clockPreserving_of_extStraightLine
#print axioms evaluate_extStraightLine_no_timeout
end InitECandidate.Runtime
