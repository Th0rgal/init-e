import InitECandidate.Runtime.SourceClock
import InitECandidate.Runtime.LocalScopeRestore
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Call-free straight syntax that leaves one chosen caller local alone. -/
def straightLocalFrame (key : MlS) : ProgHOL 64 → Bool
  | .dec name _ _ body => (name == key) || straightLocalFrame key body
  | .seq first second => straightLocalFrame key first && straightLocalFrame key second
  | .ite _ yes no => straightLocalFrame key yes && straightLocalFrame key no
  | .assign .local name _ => !(name == key)
  | .store _ _ => true
  | .skip | .break | .continue | .annot _ _ => true
  | _ => false

theorem evaluate_straight_local_frame {F : Type} (key : MlS) (program : ProgHOL 64)
    (supported : straightLocalFrame key program = true) (state : PanSemStateFiniteExact 64 F) :
    (evaluateHOLFiniteState state program).2.locals.lookup key = state.locals.lookup key := by
  cases shape : program with
  | skip => rw [evaluateHOLFiniteState_skip]
  | dec name kind initializer body =>
    rw [evaluateHOLFiniteState_dec_total]
    dsimp only
    split
    · rfl
    · rename_i value initialized
      split
      · by_cases same : name = key
        · subst name
          cases saved : state.locals.lookup key <;>
            simp [HolFiniteMapExact.resVarEq,HolFiniteMapExact.lookup_updateEq,
              HolFiniteMapExact.lookup_eraseEq,FUPDATE_HOL,FDOMSUB_HOL,saved]
        · have child : straightLocalFrame key body = true := by
            simpa [shape,straightLocalFrame,same] using supported
          rw [restore_other_local _ name key _ (Ne.symm same)]
          have frame := evaluate_straight_local_frame key body child (setVarHOLFinite name value state)
          simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,same,Ne.symm same] using frame
      · rfl
  | assign kind name value =>
    cases kind with
    | global => simp [shape,straightLocalFrame] at supported
    | «local» =>
      have different : name ≠ key := by simpa [shape,straightLocalFrame] using supported
      rw [evaluateHOLFiniteState_assign]
      split
      · rfl
      · split
        · simp [setKvarHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,different,Ne.symm different]
        · rfl
  | store destination value =>
    rw [evaluateHOLFiniteState_store]
    split <;> try rfl
    split <;> try rfl
    split <;> rfl
  | seq first second =>
    have children : straightLocalFrame key first = true ∧ straightLocalFrame key second = true := by
      simpa only [shape,straightLocalFrame,Bool.and_eq_true] using supported
    have one := evaluate_straight_local_frame key first children.1 state
    rw [evaluateHOLFiniteState_seq_line780]
    cases ran : evaluateHOLFiniteState state first with
    | mk result middle =>
      rw [ran] at one
      cases result with
      | none => exact (evaluate_straight_local_frame key second children.2 middle).trans one
      | some result => exact one
  | ite condition yes no =>
    have children : straightLocalFrame key yes = true ∧ straightLocalFrame key no = true := by
      simpa only [shape,straightLocalFrame,Bool.and_eq_true] using supported
    rw [evaluateHOLFiniteState_ite]
    split
    · split
      · exact evaluate_straight_local_frame key no children.2 state
      · exact evaluate_straight_local_frame key yes children.1 state
    · rfl
  | «break» => rw [evaluateHOLFiniteState_break]
  | «continue» => rw [evaluateHOLFiniteState_continue]
  | annot tag text => rw [evaluateHOLFiniteState_annot]
  | _ => simp [shape,straightLocalFrame] at supported
termination_by sizeOf program

#print axioms evaluate_straight_local_frame
end InitECandidate.Runtime
