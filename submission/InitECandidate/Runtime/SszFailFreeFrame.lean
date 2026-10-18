import InitECandidate.Runtime.ReadOnlyGlobals
import InitECandidate.Runtime.SszFailCallControl
import InitECandidate.Runtime.SszFailCallNoReturn
import InitECandidate.Runtime.SszFailCallTerminal
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def sszFailCallOk : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL 64)) → MlS →
    List (ExpHOL 64) → Bool
  | some (none, none), f, [.const _] => decide (f = ofString "ssz_fail")
  | _, _, _ => false

theorem sszFailCallOk_spec (info : Option (Option (VarKind × MlS) × Option (MlS × MlS × ProgHOL 64)))
    (f : MlS) (args : List (ExpHOL 64)) (ok : sszFailCallOk info f args = true) :
    info = some (none, none) ∧ f = ofString "ssz_fail" ∧ ∃ c, args = [.const c] := by
  unfold sszFailCallOk at ok
  split at ok
  · exact ⟨rfl, of_decide_eq_true ok, _, rfl⟩
  · simp at ok

/-- Read-only source syntax that may additionally reject through a literal
ssz_fail call. -/
def sszFailFree : ProgHOL 64 → Bool
  | .dec _ _ _ body => sszFailFree body
  | .seq first second => sszFailFree first && sszFailFree second
  | .ite _ yes no => sszFailFree yes && sszFailFree no
  | .while _ body => sszFailFree body
  | .assign .local _ _ => true
  | .skip | .break | .continue | .annot _ _ | .raise _ _ | .return _ => true
  | .call info f args => sszFailCallOk info f args
  | _ => false

/-- Outcomes after which execution continues in the caller. -/
def SszBenign (result : Option (PanSemResultExact 64)) : Prop :=
  result = none ∨ result = some .continue ∨ result = some .break ∨ ∃ v, result = some (.returned v)

theorem sszFail_call_not_benign {F : Type} (state : PanSemStateFiniteExact 64 F) (c : BitVec 64)
    (code : state.code = originalRuntimeCode) :
    ¬ SszBenign (evaluateHOLFiniteState state (.call (some (none,none)) (ofString "ssz_fail") [.const c])).1 := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.const c] = some [.val (.word c)] := by simp [evalListHOLFinite, evalListHOLExact, evalHOLExact]
  have terminal := evaluate_sszFail_call_terminal state (.const c) c code args
  have control := evaluate_sszFail_call_not_control state (.const c) c code args
  rintro (h | h | h | ⟨v, h⟩)
  · exact terminal h
  · exact control.2 h
  · exact control.1 h
  · exact evaluate_sszFail_call_no_return state (.const c) c v code args h

/-- Benign executions of ssz_fail-free code preserve memory and globals. -/
theorem evaluate_sszFailFree_frame {F : Type} (program : ProgHOL 64)
    (supported : sszFailFree program = true) (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) :
    SszBenign (evaluateHOLFiniteState state program).1 →
    (evaluateHOLFiniteState state program).2.memory = state.memory ∧
      (evaluateHOLFiniteState state program).2.globals = state.globals := by
  cases shape : program with
  | skip => rw [evaluateHOLFiniteState_skip]; intro _; exact ⟨rfl, rfl⟩
  | dec name kind initializer body =>
    have child : sszFailFree body = true := by simpa only [shape, sszFailFree] using supported
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · intro _; exact ⟨rfl, rfl⟩
    · split
      · exact evaluate_sszFailFree_frame body child _ code
      · intro _; exact ⟨rfl, rfl⟩
  | assign kind name value =>
    cases kind with
    | global => simp [shape, sszFailFree] at supported
    | «local» =>
      rw [evaluateHOLFiniteState_assign]
      split
      · intro _; exact ⟨rfl, rfl⟩
      · split <;> intro _ <;> exact ⟨rfl, rfl⟩
  | seq first second =>
    have children : sszFailFree first = true ∧ sszFailFree second = true := by
      simpa only [shape, sszFailFree, Bool.and_eq_true] using supported
    have remaining := evaluateHOLFiniteState_clock_le state first
    have metadata := evaluateHOLFiniteState_metadata state first
    have firstFrame := evaluate_sszFailFree_frame first children.1 state code
    rw [evaluateHOLFiniteState_seq_line780]
    cases firstRun : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [firstRun] at remaining metadata firstFrame
      dsimp only at remaining metadata firstFrame ⊢
      intro benign
      cases result with
      | none =>
        obtain ⟨m1, g1⟩ := firstFrame (Or.inl rfl)
        obtain ⟨m2, g2⟩ := evaluate_sszFailFree_frame second children.2 middle (metadata.1.trans code) benign
        exact ⟨m2.trans m1, g2.trans g1⟩
      | some result => exact firstFrame benign
  | ite condition yes no =>
    have children : sszFailFree yes = true ∧ sszFailFree no = true := by
      simpa only [shape, sszFailFree, Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_sszFailFree_frame no children.2 state code
      · exact evaluate_sszFailFree_frame yes children.1 state code
    · intro _; exact ⟨rfl, rfl⟩
  | «while» condition body =>
    have child : sszFailFree body = true := by simpa only [shape, sszFailFree] using supported
    have loopFree : sszFailFree (.while condition body) = true := by simpa [sszFailFree] using child
    rw [evaluateHOLFiniteState_while_total]
    split
    · split
      · split
        · intro _; exact ⟨rfl, rfl⟩
        · rename_i nonzero
          dsimp only
          rw [fixClockHOLFinite_evaluateState]
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          have metadata := evaluateHOLFiniteState_metadata (decClockHOLFinite state) body
          have bodyFrame := evaluate_sszFailFree_frame body child (decClockHOLFinite state) code
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk result middle =>
            rw [bodyRun] at remaining metadata bodyFrame
            dsimp only at remaining metadata bodyFrame ⊢
            have smaller : middle.clock < state.clock := by
              change middle.clock ≤ state.clock - 1 at remaining
              omega
            have middleCode : middle.code = originalRuntimeCode := metadata.1.trans code
            intro benign
            cases result with
            | none =>
              obtain ⟨m1, g1⟩ := bodyFrame (Or.inl rfl)
              obtain ⟨m2, g2⟩ := evaluate_sszFailFree_frame (.while condition body) loopFree middle middleCode benign
              exact ⟨m2.trans m1, g2.trans g1⟩
            | some result =>
              cases result with
              | «continue» =>
                obtain ⟨m1, g1⟩ := bodyFrame (Or.inr (Or.inl rfl))
                obtain ⟨m2, g2⟩ := evaluate_sszFailFree_frame (.while condition body) loopFree middle middleCode benign
                exact ⟨m2.trans m1, g2.trans g1⟩
              | «break» => exact bodyFrame (Or.inr (Or.inr (Or.inl rfl)))
              | returned value => exact bodyFrame (Or.inr (Or.inr (Or.inr ⟨value, rfl⟩)))
              | exception exception value => simp [SszBenign] at benign
              | finalFfi ffi => simp [SszBenign] at benign
              | error => simp [SszBenign] at benign
              | timeOut => simp [SszBenign] at benign
      · intro _; exact ⟨rfl, rfl⟩
    · intro _; exact ⟨rfl, rfl⟩
  | «break» => rw [evaluateHOLFiniteState_break]; intro _; exact ⟨rfl, rfl⟩
  | «continue» => rw [evaluateHOLFiniteState_continue]; intro _; exact ⟨rfl, rfl⟩
  | annot tag text => rw [evaluateHOLFiniteState_annot]; intro _; exact ⟨rfl, rfl⟩
  | raise name value =>
    rw [evaluateHOLFiniteState_raise]
    split
    · dsimp only; split <;> intro _ <;> exact ⟨rfl, rfl⟩
    · intro _; exact ⟨rfl, rfl⟩
  | «return» value =>
    rw [evaluateHOLFiniteState_return]
    split
    · intro _; exact ⟨rfl, rfl⟩
    · split <;> intro _ <;> exact ⟨rfl, rfl⟩
  | call info f arguments =>
    intro benign
    exfalso
    obtain ⟨rfl, rfl, c, rfl⟩ := sszFailCallOk_spec info f arguments (by simpa only [shape, sszFailFree] using supported)
    exact sszFail_call_not_benign state c code benign
  | _ => simp [shape, sszFailFree] at supported
termination_by (state.clock, sizeOf program)
decreasing_by all_goals simp_all [decClockHOLFinite, setVarHOLFinite] <;> omega

#print axioms evaluate_sszFailFree_frame
end InitECandidate.Runtime
