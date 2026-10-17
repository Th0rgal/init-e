import InitECandidate.Runtime.StoreControlFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Normal completion past a store exposes a successful store preserving
all caller locals, followed by the actual normal continuation. -/
theorem evaluate_store_sequence_normal {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (destination value : ExpHOL 64) (tail : ProgHOL 64)
    (run : evaluateHOLFiniteState state (.seq (.store destination value) tail) = (none,post)) :
    ∃ middle, evaluateHOLFiniteState state (.store destination value) = (none,middle) ∧
      middle.locals = state.locals ∧ evaluateHOLFiniteState middle tail = (none,post) := by
  have facts := evaluate_store_control_frame state destination value
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases stored : evaluateHOLFiniteState state (.store destination value) with
  | mk result middle =>
    rw [stored] at facts run
    obtain ⟨control,locals,_⟩ := facts
    rcases control with rfl | rfl
    · exact ⟨middle,rfl,locals,run⟩
    · cases run

#print axioms evaluate_store_sequence_normal
end InitECandidate.Runtime
