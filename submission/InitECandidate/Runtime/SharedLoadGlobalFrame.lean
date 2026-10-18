import InitECandidate.Runtime.ReadOnlyMemory
import InitECandidate.Runtime.SharedLoadControlFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Call-free syntax including local shared loads retains a watched global. -/
def avoidsGlobalAssignmentWithSharedLoad (watched : MlS) : ProgHOL 64 → Bool
  | .dec _ _ _ body => avoidsGlobalAssignmentWithSharedLoad watched body
  | .seq first second => avoidsGlobalAssignmentWithSharedLoad watched first && avoidsGlobalAssignmentWithSharedLoad watched second
  | .ite _ yes no => avoidsGlobalAssignmentWithSharedLoad watched yes && avoidsGlobalAssignmentWithSharedLoad watched no
  | .while _ body => avoidsGlobalAssignmentWithSharedLoad watched body
  | .assign .global name _ => !(name == watched)
  | .assign .local _ _ => true
  | .store _ _ | .storeByte _ _ => true
  | .shMemLoad _ .local _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | _ => false

/-- The checker excludes assignments to the watched global, so its binding
is unchanged at every fuel, including failed and interrupted outcomes. -/
theorem evaluate_avoidsGlobalAssignmentWithSharedLoad {F : Type} (watched : MlS) (program : ProgHOL 64)
    (supported : avoidsGlobalAssignmentWithSharedLoad watched program = true) (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state program).2.globals.lookup watched = state.globals.lookup watched := by
  cases shape : program with
  | skip => rw [evaluateHOLFiniteState_skip]
  | dec name kind initializer body =>
    have child : avoidsGlobalAssignmentWithSharedLoad watched body = true := by simpa only [shape,avoidsGlobalAssignmentWithSharedLoad] using supported
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · rfl
    · split
      · exact evaluate_avoidsGlobalAssignmentWithSharedLoad watched body child _
      · rfl
  | assign kind name value =>
    cases kind with
    | global =>
      have different : name ≠ watched := by simpa [shape,avoidsGlobalAssignmentWithSharedLoad] using supported
      rw [evaluateHOLFiniteState_assign]
      split
      · rfl
      · split
        · simp [setKvarHOLFinite,setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different]
        · rfl
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · rfl
      · split <;> rfl
  | seq first second =>
    have children : avoidsGlobalAssignmentWithSharedLoad watched first = true ∧ avoidsGlobalAssignmentWithSharedLoad watched second = true := by
      simpa only [shape,avoidsGlobalAssignmentWithSharedLoad,Bool.and_eq_true] using supported
    have memory := evaluate_avoidsGlobalAssignmentWithSharedLoad watched first children.1 state
    have remaining := evaluateHOLFiniteState_clock_le state first
    rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at memory remaining
      dsimp only at memory remaining
      cases result with
      | none => exact (evaluate_avoidsGlobalAssignmentWithSharedLoad watched second children.2 middle).trans memory
      | some result => exact memory
  | ite condition yes no =>
    have children : avoidsGlobalAssignmentWithSharedLoad watched yes = true ∧ avoidsGlobalAssignmentWithSharedLoad watched no = true := by
      simpa only [shape,avoidsGlobalAssignmentWithSharedLoad,Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_avoidsGlobalAssignmentWithSharedLoad watched no children.2 state
      · exact evaluate_avoidsGlobalAssignmentWithSharedLoad watched yes children.1 state
    · rfl
  | «while» condition body =>
    have child : avoidsGlobalAssignmentWithSharedLoad watched body = true := by simpa only [shape,avoidsGlobalAssignmentWithSharedLoad] using supported
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · rfl
        · rename_i nonzero
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have memory := evaluate_avoidsGlobalAssignmentWithSharedLoad watched body child (decClockHOLFinite state)
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk result middle =>
            rw [bodyRun] at memory remaining
            dsimp only at memory remaining
            have smaller : middle.clock < state.clock := by
              change middle.clock ≤ state.clock - 1 at remaining
              omega
            cases result with
            | none => exact (evaluate_avoidsGlobalAssignmentWithSharedLoad watched (.while condition body) (by simpa [avoidsGlobalAssignmentWithSharedLoad] using child) middle).trans memory
            | some result =>
              cases result with
              | «continue» => exact (evaluate_avoidsGlobalAssignmentWithSharedLoad watched (.while condition body) (by simpa [avoidsGlobalAssignmentWithSharedLoad] using child) middle).trans memory
              | «break» => exact memory
              | returned value => exact memory
              | exception exception value => exact memory
              | finalFfi ffi => exact memory
              | error => exact memory
              | timeOut => exact memory
      · rfl
    · rfl
  | «break» => rw [evaluateHOLFiniteState_break]
  | «continue» => rw [evaluateHOLFiniteState_continue]
  | annot tag text => rw [evaluateHOLFiniteState_annot]
  | raise name value =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> rfl
    · rfl
  | «return» value =>
    rw [evaluateHOLFiniteState_return]
    split
    · rfl
    · split <;> rfl
  | store destination value =>
    rw [evaluateHOLFiniteState_store]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | storeByte destination value =>
    rw [evaluateHOLFiniteState_storeByte]
    split
    · split
      · split <;> simp
      · simp
    · simp
  | shMemLoad operator kind name address =>
    cases kind with
    | global => simp [shape,avoidsGlobalAssignmentWithSharedLoad] at supported
    | «local» =>
      exact congrArg (fun globals => globals.lookup watched)
        (evaluate_shared_load_control_frame state operator name address).2.2.1
  | _ => simp [shape,avoidsGlobalAssignmentWithSharedLoad] at supported
termination_by (state.clock,sizeOf program)
decreasing_by all_goals simp_all [decClockHOLFinite,setVarHOLFinite] <;> omega


#print axioms evaluate_avoidsGlobalAssignmentWithSharedLoad
end InitECandidate.Runtime
