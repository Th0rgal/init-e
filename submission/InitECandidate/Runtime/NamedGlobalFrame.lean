import InitECandidate.Runtime.ReadOnlyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Call-free syntax may update other globals while retaining a watched global. -/
def avoidsGlobalAssignment (watched : MlS) : ProgHOL 64 → Bool
  | .dec _ _ _ body => avoidsGlobalAssignment watched body
  | .seq first second => avoidsGlobalAssignment watched first && avoidsGlobalAssignment watched second
  | .ite _ yes no => avoidsGlobalAssignment watched yes && avoidsGlobalAssignment watched no
  | .while _ body => avoidsGlobalAssignment watched body
  | .assign .global name _ => !(name == watched)
  | .assign .local _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | _ => false

/-- The checker excludes assignments to the watched global, so its binding
is unchanged at every fuel, including failed and interrupted outcomes. -/
theorem evaluate_avoidsGlobalAssignment {F : Type} (watched : MlS) (program : ProgHOL 64)
    (supported : avoidsGlobalAssignment watched program = true) (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state program).2.globals.lookup watched = state.globals.lookup watched := by
  cases shape : program with
  | skip => rw [evaluateHOLFiniteState_skip]
  | dec name kind initializer body =>
    have child : avoidsGlobalAssignment watched body = true := by simpa only [shape,avoidsGlobalAssignment] using supported
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · rfl
    · split
      · exact evaluate_avoidsGlobalAssignment watched body child _
      · rfl
  | assign kind name value =>
    cases kind with
    | global =>
      have different : name ≠ watched := by simpa [shape,avoidsGlobalAssignment] using supported
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
    have children : avoidsGlobalAssignment watched first = true ∧ avoidsGlobalAssignment watched second = true := by
      simpa only [shape,avoidsGlobalAssignment,Bool.and_eq_true] using supported
    have memory := evaluate_avoidsGlobalAssignment watched first children.1 state
    have remaining := evaluateHOLFiniteState_clock_le state first
    rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at memory remaining
      dsimp only at memory remaining
      cases result with
      | none => exact (evaluate_avoidsGlobalAssignment watched second children.2 middle).trans memory
      | some result => exact memory
  | ite condition yes no =>
    have children : avoidsGlobalAssignment watched yes = true ∧ avoidsGlobalAssignment watched no = true := by
      simpa only [shape,avoidsGlobalAssignment,Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_avoidsGlobalAssignment watched no children.2 state
      · exact evaluate_avoidsGlobalAssignment watched yes children.1 state
    · rfl
  | «while» condition body =>
    have child : avoidsGlobalAssignment watched body = true := by simpa only [shape,avoidsGlobalAssignment] using supported
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · rfl
        · rename_i nonzero
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have memory := evaluate_avoidsGlobalAssignment watched body child (decClockHOLFinite state)
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk result middle =>
            rw [bodyRun] at memory remaining
            dsimp only at memory remaining
            have smaller : middle.clock < state.clock := by
              change middle.clock ≤ state.clock - 1 at remaining
              omega
            cases result with
            | none => exact (evaluate_avoidsGlobalAssignment watched (.while condition body) (by simpa [avoidsGlobalAssignment] using child) middle).trans memory
            | some result =>
              cases result with
              | «continue» => exact (evaluate_avoidsGlobalAssignment watched (.while condition body) (by simpa [avoidsGlobalAssignment] using child) middle).trans memory
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
  | _ => simp [shape,avoidsGlobalAssignment] at supported
termination_by (state.clock,sizeOf program)
decreasing_by all_goals simp_all [decClockHOLFinite,setVarHOLFinite] <;> omega


#print axioms evaluate_avoidsGlobalAssignment
end InitECandidate.Runtime
