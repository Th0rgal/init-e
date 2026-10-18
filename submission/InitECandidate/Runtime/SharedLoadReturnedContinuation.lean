import InitECandidate.Runtime.SharedLoadControlFrame
import InitECandidate.Runtime.PanEvaluationMetadata
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A returned continuation after a shared load necessarily followed a
normal word read; the source memory, globals, code and domain are retained. -/
theorem shared_load_returned_continuation {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (operator : OpSize) (name : MlS) (address : ExpHOL 64) (tail : ProgHOL 64) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState state (.seq (.shMemLoad operator .local name address) tail) =
      (some (.returned value),post)) :
    ∃ (ready : PanSemStateFiniteExact 64 F) (word : BitVec 64),
      evaluateHOLFiniteState ready tail = (some (.returned value),post) ∧
      ready.locals.lookup name = some (.val (.word word)) ∧ ready.globals = state.globals ∧
      ready.memory = state.memory ∧ ready.memaddrs = state.memaddrs ∧ ready.code = state.code := by
  have frame := evaluate_shared_load_control_frame state operator name address
  have metadata := evaluateHOLFiniteState_metadata state (.shMemLoad operator .local name address)
  rw [evaluateHOLFiniteState_seq_line780] at run
  cases loaded : evaluateHOLFiniteState state (.shMemLoad operator .local name address) with
  | mk result ready =>
    rw [loaded] at run frame metadata
    dsimp only at frame metadata
    obtain ⟨_,control,globals,memory,domain,normal⟩ := frame
    rcases control with rfl | rfl | ⟨event,rfl⟩
    · obtain ⟨word,atWord,_⟩ := normal rfl
      exact ⟨ready,word,run,atWord,globals,memory,domain,metadata.1⟩
    · cases run
    · cases run

#print axioms shared_load_returned_continuation
end InitECandidate.Runtime
