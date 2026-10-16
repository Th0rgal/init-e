import InitECandidate.Runtime.HashTableArraysFind32
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Two summaries of the same declaration must bind the same word. A return
of the bound local distinguishes the results without assumptions on clocks. -/
theorem declaration_word_result_unique {F : Type}
    (state left right : PanSemStateFiniteExact 64 F) (name function : MlS)
    (arguments : List (ExpHOL 64)) (first second : BitVec 64)
    (leftRun : ∀ continuation, evaluateHOLFiniteState state (.decCall name .one function arguments continuation) =
      (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word first)) left) continuation;
       (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name)})))
    (rightRun : ∀ continuation, evaluateHOLFiniteState state (.decCall name .one function arguments continuation) =
      (let output := evaluateHOLFiniteState (setVarHOLFinite name (.val (.word second)) right) continuation;
       (output.1,{output.2 with locals := HolFiniteMapExact.resVarEq output.2.locals (name,state.locals.lookup name)}))) :
    first = second := by
  have equal := congrArg Prod.fst ((leftRun (.return (.var .local name))).symm.trans (rightRun (.return (.var .local name))))
  simp [evaluateHOLFiniteState_return,evalHOLExact,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,shapeOfHOLExact] at equal
  exact equal

#print axioms declaration_word_result_unique
end InitECandidate.Runtime
