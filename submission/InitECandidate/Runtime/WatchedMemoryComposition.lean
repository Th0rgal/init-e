import InitECandidate.Runtime.WordStoreMemoryFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem watched_memory_seq {F : Type} (state : PanSemStateFiniteExact 64 F)
    (first tail : ProgHOL 64) (watched : BitVec 64)
    (frame : (evaluateHOLFiniteState state first).2.memory watched = state.memory watched)
    (rest : ∀ next, evaluateHOLFiniteState state first = (none,next) →
      (evaluateHOLFiniteState next tail).2.memory watched = next.memory watched) :
    (evaluateHOLFiniteState state (.seq first tail)).2.memory watched = state.memory watched := by
  rw [evaluateHOLFiniteState_seq_line780]
  cases run : evaluateHOLFiniteState state first with
  | mk result next =>
    rw [run] at frame
    cases result with
    | none => exact (rest next run).trans frame
    | some result => exact frame

theorem watched_memory_dec {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (shape : ShapeHOL) (initializer : ExpHOL 64) (body : ProgHOL 64) (watched : BitVec 64)
    (frame : ∀ value : ValueHOL 64,
      (evaluateHOLFiniteState (setVarHOLFinite name value state) body).2.memory watched = state.memory watched) :
    (evaluateHOLFiniteState state (.dec name shape initializer body)).2.memory watched = state.memory watched := by
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  split
  · rfl
  · split
    · exact frame _
    · rfl

#print axioms watched_memory_seq
#print axioms watched_memory_dec
end InitECandidate.Runtime
