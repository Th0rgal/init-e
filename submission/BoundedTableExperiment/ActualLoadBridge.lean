import CandidateFindLeafShape
import ActualLinkMemoryInvariant
import InitECandidate.Runtime.LoadOneRead
import InitECandidate.Runtime.RlpPutBeMemoryWindow

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 1000000

/-- Evaluate a `local + offset` address ending in the expected word. -/
theorem eval_localAddr {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (base offset : BitVec 64)
    (hlocal : s.locals.lookup name = some (.val (.word base))) :
    expressionValue s (localAddr name offset) =
      some (.val (.word (base + offset))) := by
  simp [localAddr, expressionValue, evalHOLExact, evalListHOLExact, hlocal,
    wordOpHOL, wordOp, valueIsWord, valueWord]

/-- Evaluate a bare local word (the zero arm's address). -/
theorem eval_localWord {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (word : BitVec 64)
    (hlocal : s.locals.lookup name = some (.val (.word word))) :
    expressionValue s (.var .local name) = some (.val (.word word)) := by
  simpa [expressionValue, evalHOLExact] using hlocal

/-- Concrete `.dec` split of `candidateFindLeafRoute`. -/
theorem candidateFindLeafRoute_dec_split {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s candidateFindLeafRoute none post events) :
    ∃ (value : ValueHOL 64) (initEvents bodyEvents : List WorkEvent)
      (bodyPost : PanSemStateFiniteExact 64 F),
      events = .statement :: (initEvents ++ [.frame 1] ++ bodyEvents) ∧
      CostedExpressionRun s (.load .one (localAddr (ofString "node") 16))
        (some value) initEvents ∧
      post = { bodyPost with locals :=
        (HolFiniteMapExact.resVarEq bodyPost.locals
          (ofString "route", s.locals.lookup (ofString "route"))) } ∧
      StatementRun fn (setVarHOLFinite (ofString "route") value s)
        candidateFindLeafByte none bodyPost bodyEvents := by
  rw [candidateFindLeaf_route] at run
  cases run with
  | declareValue init shapeMatch bodyRun =>
      exact ⟨_, _, _, _, rfl, init, rfl, bodyRun⟩

/-- The route variable is the actual word at `node + 16`. -/
theorem candidateFindLeafRoute_route {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    {node left right route : BitVec 64}
    (run : StatementRun fn s candidateFindLeafRoute none post events)
    (inv : NodeLinkInv s node left right route)
    (nodeLocal : s.locals.lookup (ofString "node") = some (.val (.word node))) :
    ∃ (initEvents bodyEvents : List WorkEvent)
      (bodyPost : PanSemStateFiniteExact 64 F),
      events = .statement :: (initEvents ++ [.frame 1] ++ bodyEvents) ∧
      CostedExpressionRun s (.load .one (localAddr (ofString "node") 16))
        (some (.val (.word route))) initEvents ∧
      post = { bodyPost with locals :=
        (HolFiniteMapExact.resVarEq bodyPost.locals
          (ofString "route", s.locals.lookup (ofString "route"))) } ∧
      StatementRun fn
        (setVarHOLFinite (ofString "route") (.val (.word route)) s)
        candidateFindLeafByte none bodyPost bodyEvents ∧
      s.memaddrs (node + 16) := by
  obtain ⟨value, initEvents, bodyEvents, bodyPost, eventsEq, init, postEq, bodyRun⟩ :=
    candidateFindLeafRoute_dec_split run
  have loaded := init.sound
  unfold expressionValue at loaded
  obtain ⟨pointer, word, addrEval, dom, cell, valueEq⟩ :=
    eval_load_one_read s (localAddr (ofString "node") 16) value loaded
  have addrWord := eval_localAddr s (ofString "node") node 16 nodeLocal
  have addrEval' :
      @evalHOLExact 64 F _ s.toExact
        (fun a => Classical.propDecidable (s.memaddrs a))
        (localAddr (ofString "node") 16) =
        some (.val (.word (node + 16))) := by
    simpa [expressionValue] using addrWord
  have pointerEq : pointer = node + 16 :=
    HolWordLab.word.inj
      (ValueHOL.val.inj (Option.some.inj (addrEval.symm.trans addrEval')))
  have wordEq : word = route := by
    rw [pointerEq, inv.routeAt] at cell
    exact (HolWordLab.word.inj cell).symm
  have valueEq' : value = .val (.word route) := by
    simpa [wordEq] using valueEq
  refine ⟨initEvents, bodyEvents, bodyPost, eventsEq, ?_, postEq, ?_, ?_⟩
  · simpa [valueEq'] using init
  · simpa [valueEq'] using bodyRun
  · simpa [pointerEq] using dom

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidateFindLeafRoute_dec_split
#print axioms BoundedTableExperiment.candidateFindLeafRoute_route
