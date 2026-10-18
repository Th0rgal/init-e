import InitECandidate.Runtime.NoTopContinue
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Programs that cannot finish with an outer-level `break` (inner loops own theirs). -/
def noTopBreak : ProgHOL 64 → Bool
  | .break => false
  | .seq first second => noTopBreak first && noTopBreak second
  | .ite _ yes no => noTopBreak yes && noTopBreak no
  | .dec _ _ _ body => noTopBreak body
  | .decCall _ _ _ _ continuation => noTopBreak continuation
  | .skip | .assign _ _ _ | .primitive _ _ _ | .store _ _ | .storeByte _ _ | .raise _ _ | .return _
  | .extCall _ _ _ _ _ | .annot _ _ | .while _ _ | .continue => true
  | .call none _ _ | .call (some (_,none)) _ _ => true
  | _ => false

theorem evaluate_noTopBreak {F : Type} (program : ProgHOL 64) (supported : noTopBreak program = true)
    (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state program).1 ≠ some .break := by
  cases shape : program with
  | «break» => simp [shape,noTopBreak] at supported
  | seq first second =>
    have children : noTopBreak first = true ∧ noTopBreak second = true := by
      simpa only [shape,noTopBreak,Bool.and_eq_true] using supported
    have remaining := evaluateHOLFiniteState_clock_le state first
    rw [evaluateHOLFiniteState_seq_line780]
    have one := evaluate_noTopBreak first children.1 state
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at one remaining
      cases result with
      | none => exact evaluate_noTopBreak second children.2 middle
      | some r => exact one
  | ite condition yes no =>
    have children : noTopBreak yes = true ∧ noTopBreak no = true := by
      simpa only [shape,noTopBreak,Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_noTopBreak no children.2 state
      · exact evaluate_noTopBreak yes children.1 state
    · simp
  | dec name kind initializer body =>
    have child : noTopBreak body = true := by simpa only [shape,noTopBreak] using supported
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · simp
    · split
      · exact evaluate_noTopBreak body child _
      · simp
  | decCall name shape' function arguments continuation =>
    have child : noTopBreak continuation = true := by simpa only [shape,noTopBreak] using supported
    intro hcont
    cases run : evaluateHOLFiniteState state (.decCall name shape' function arguments continuation) with
    | mk result post =>
      rw [run] at hcont
      dsimp only at hcont
      subst hcont
      obtain ⟨w,resumed,inner,_,smaller,contRun,_⟩ := decCall_flowing (Or.inr (Or.inl rfl)) run
      have := evaluate_noTopBreak continuation child resumed
      rw [contRun] at this
      exact this rfl
  | skip => simp [evaluateHOLFiniteState_skip]
  | «continue» => simp [evaluateHOLFiniteState_continue]
  | annot tag text => simp [evaluateHOLFiniteState_annot]
  | raise name value =>
    rw [evaluateHOLFiniteState_raise]; split
    · dsimp only; split <;> simp
    · simp
  | «return» value =>
    rw [evaluateHOLFiniteState_return]; split
    · simp
    · split <;> simp
  | store destination value => rcases (evaluate_store_control_frame state destination value).1 with h | h <;> rw [h] <;> simp
  | storeByte destination value => rcases (evaluate_storeByte_control_frame state destination value).1 with h | h <;> rw [h] <;> simp
  | assign kind name value =>
    rw [evaluateHOLFiniteState_assign]; split
    · simp
    · split <;> simp
  | primitive name operator arguments =>
    rw [evaluateHOLFiniteState_primitive]
    repeat' first | split | simp
  | extCall function a b c d =>
    rw [evaluateHOLFiniteState_extCall_source]
    repeat' first | split | simp
  | call info function arguments =>
    have handlerFree : info = none ∨ ∃ d, info = some (d,none) := by
      rcases info with _ | ⟨d,_ | h⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨d,rfl⟩
      · simp [shape,noTopBreak] at supported
    rw [evaluateHOLFiniteState_call]
    rcases handlerFree with rfl | ⟨d,rfl⟩
    all_goals dsimp only
    all_goals repeat' first | split | simp | simp_all
  | «while» condition body =>
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · simp
        · rename_i nonzero
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk result middle =>
            rw [bodyRun] at remaining
            have smaller : middle.clock < state.clock := by
              change middle.clock ≤ state.clock - 1 at remaining
              omega
            cases result with
            | none => exact evaluate_noTopBreak (.while condition body) (by simp [noTopBreak]) middle
            | some result =>
              cases result with
              | «continue» => exact evaluate_noTopBreak (.while condition body) (by simp [noTopBreak]) middle
              | _ => simp
      · simp
    · simp
  | _ => simp [shape,noTopBreak] at supported
termination_by (state.clock,sizeOf program)
decreasing_by all_goals simp_all [decClockHOLFinite,setVarHOLFinite] <;> omega

#print axioms evaluate_noTopBreak
end InitECandidate.Runtime
