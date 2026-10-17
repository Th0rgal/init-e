import InitECandidate.Runtime.ReadOnlyMemory
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The same call-free syntax excludes global assignments, so its global map
is unchanged at every fuel, including all failed and interrupted outcomes. -/
theorem evaluate_readOnly_globals {F : Type} (program : ProgHOL 64)
    (supported : readOnlyMemory program = true) (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state program).2.globals = state.globals := by
  cases shape : program with
  | skip => rw [evaluateHOLFiniteState_skip]
  | dec name kind initializer body =>
    have child : readOnlyMemory body = true := by simpa only [shape,readOnlyMemory] using supported
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · rfl
    · split
      · exact evaluate_readOnly_globals body child _
      · rfl
  | assign kind name value =>
    cases kind with
    | global => simp [shape,readOnlyMemory] at supported
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · rfl
      · split <;> rfl
  | seq first second =>
    have children : readOnlyMemory first = true ∧ readOnlyMemory second = true := by
      simpa only [shape,readOnlyMemory,Bool.and_eq_true] using supported
    have memory := evaluate_readOnly_globals first children.1 state
    have remaining := evaluateHOLFiniteState_clock_le state first
    rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at memory remaining
      dsimp only at memory remaining
      cases result with
      | none => exact (evaluate_readOnly_globals second children.2 middle).trans memory
      | some result => exact memory
  | ite condition yes no =>
    have children : readOnlyMemory yes = true ∧ readOnlyMemory no = true := by
      simpa only [shape,readOnlyMemory,Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_readOnly_globals no children.2 state
      · exact evaluate_readOnly_globals yes children.1 state
    · rfl
  | «while» condition body =>
    have child : readOnlyMemory body = true := by simpa only [shape,readOnlyMemory] using supported
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · rfl
        · rename_i nonzero
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have memory := evaluate_readOnly_globals body child (decClockHOLFinite state)
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk result middle =>
            rw [bodyRun] at memory remaining
            dsimp only at memory remaining
            have smaller : middle.clock < state.clock := by
              change middle.clock ≤ state.clock - 1 at remaining
              omega
            cases result with
            | none => exact (evaluate_readOnly_globals (.while condition body) (by simpa [readOnlyMemory] using child) middle).trans memory
            | some result =>
              cases result with
              | «continue» => exact (evaluate_readOnly_globals (.while condition body) (by simpa [readOnlyMemory] using child) middle).trans memory
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
  | _ => simp [shape,readOnlyMemory] at supported
termination_by (state.clock,sizeOf program)
decreasing_by all_goals simp_all [decClockHOLFinite,setVarHOLFinite] <;> omega


#print axioms evaluate_readOnly_globals
end InitECandidate.Runtime
