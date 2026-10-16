import InitECandidate.Runtime.ZeroGlobalDeclarations
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact Flapjack.Pancake.PanLang

/-- Source global initialization changes exactly the global map. -/
theorem zero_global_post_frame {width : Nat} [NeZero width] {F : Type}
    (names : List MlS) (state : PanSemStateFiniteExact width F) :
    zeroGlobalPost state names =
      {state with globals := names.foldl (fun globals name => globals.update (name,.val (.word 0))) state.globals} := by
  induction names generalizing state with
  | nil => rfl
  | cons name names ih =>
    change zeroGlobalPost (setGlobalHOLFinite name (.val (.word 0)) state) names = _
    rw [ih]
    rfl

#print axioms zero_global_post_frame
end InitECandidate.Runtime
