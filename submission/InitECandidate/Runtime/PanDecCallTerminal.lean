import InitECandidate.Runtime.PanDecCallNormalReturnProperty
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A declaration call whose continuation always terminates cannot fall through.
Argument, lookup, clock and return-shape failures are terminal too. -/
theorem evaluate_decCall_terminal {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name function : MlS) (shape : ShapeHOL) (arguments : List (ExpHOL 64))
    (continuation : ProgHOL 64)
    (terminal : ∀ current : PanSemStateFiniteExact 64 F,
      (evaluateHOLFiniteState current continuation).1 ≠ none) :
    (evaluateHOLFiniteState state (.decCall name shape function arguments continuation)).1 ≠ none := by
  intro normal
  cases run : evaluateHOLFiniteState state (.decCall name shape function arguments continuation) with
  | mk result post =>
    rw [run] at normal
    change result = none at normal
    subst result
    cases args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments with
    | none => rw [evaluateHOLFiniteState_decCall_total,args] at run; cases run
    | some values =>
      cases lookup : lookupCodeHOLFinite state.code.lookup function values with
      | none => rw [evaluateHOLFiniteState_decCall_total,args] at run; dsimp only at run; rw [lookup] at run; cases run
      | some installed =>
        obtain ⟨body,callee,returnShape⟩ := installed
        obtain ⟨value,ready,output,_,_,tail,_⟩ := evaluate_decCall_normal_return_property state post name function
          shape returnShape arguments values body continuation callee args lookup (fun _ => True)
          (by intro _ _ _; trivial) run
        have impossible := terminal (setVarHOLFinite name value ready)
        rw [tail] at impossible
        exact impossible rfl

#print axioms evaluate_decCall_terminal
end InitECandidate.Runtime
