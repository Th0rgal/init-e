import CandidateFindLeafStepTrace
import CandidateFindLeafPush
import InitECandidate.Runtime.RlpPutBeMemoryWindow
import ActualTaggedTrie

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 1000000

/-- A successful `candidateFindLeafGuard` run is the skip branch and leaves the
state unchanged. -/
theorem candidateFindLeafGuard_skip {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s candidateFindLeafGuard none post events) :
    post = s := by
  rw [show candidateFindLeafGuard =
    .ite (.cmp .notLower (.var .local (ofString "cap")) (.var .local (ofString "node")))
      (.seq (.store (localAddr (ofString "t") 112) (.var .local (ofString "depth")))
        (.return (.var .local (ofString "node"))))
      .skip from rfl] at run
  cases run with
  | iteYes guard nonzero body =>
      cases body with
      | seqNext one two => cases two
      | seqStop terminal one => exact absurd rfl terminal
  | iteNo guard body =>
      cases body with
      | skip s => rfl


/-- The skip comparison evaluates to `0` exactly when the node is above the
cap threshold, i.e. it is an internal node. -/
theorem eval_candidateFindLeafGuard {F : Type} (s : PanSemStateFiniteExact 64 F)
    (cap node : BitVec 64)
    (capLocal : s.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (nodeLocal : s.locals.lookup (ofString "node") = some (.val (.word node))) :
    expressionValue s (.cmp .notLower (.var .local (ofString "cap"))
      (.var .local (ofString "node"))) =
      some (.val (.word (if BitVec.ult cap node then 0 else 1))) := by
  simp only [expressionValue, evalHOLExact, capLocal, nodeLocal,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL]
  by_cases h : cap < node
  · have hle : ¬ node ≤ cap := by simpa [BitVec.le_def] using (not_le.mpr h)
    simp [BitVec.ult, hle]
    exact h
  · have hle : node ≤ cap := by simpa [BitVec.le_def] using (le_of_not_gt h)
    simp [BitVec.ult, hle]
    exact hle

/-- A successful guard run on a real `(cap, node)` pair comes from the skip
branch, so the node is internal; it leaves the state unchanged. -/
theorem candidateFindLeafGuard_internal {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    {cap node : BitVec 64}
    (run : StatementRun fn s candidateFindLeafGuard none post events)
    (capLocal : s.locals.lookup (ofString "cap") = some (.val (.word cap)))
    (nodeLocal : s.locals.lookup (ofString "node") = some (.val (.word node))) :
    post = s ∧ IsInternal cap node := by
  rw [show candidateFindLeafGuard =
    .ite (.cmp .notLower (.var .local (ofString "cap")) (.var .local (ofString "node")))
      (.seq (.store (localAddr (ofString "t") 112) (.var .local (ofString "depth")))
        (.return (.var .local (ofString "node"))))
      .skip from rfl] at run
  cases run with
  | iteYes guard nonzero body =>
      cases body with
      | seqNext one two => cases two
      | seqStop terminal one => exact absurd rfl terminal
  | iteNo guard body =>
      cases body with
      | skip s =>
          refine ⟨rfl, ?_⟩
          have gs := guard.sound
          unfold expressionValue at gs
          have ev := eval_candidateFindLeafGuard s cap node capLocal nodeLocal
          unfold expressionValue at ev
          rw [gs] at ev
          have hzero : (0#64) = (if BitVec.ult cap node then (0#64) else (1#64)) :=
            HolWordLab.word.inj (ValueHOL.val.inj (Option.some.inj ev))
          by_cases h : BitVec.ult cap node
          · exact h
          · simp [h] at hzero

/-- The path push changes only memory; the node local is untouched. -/
theorem candidateFindLeafPush_preserves_node {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    (run : StatementRun fn s candidateFindLeafPush none post events) :
    post.locals.lookup (ofString "node") = s.locals.lookup (ofString "node") := by
  change StatementRun fn s
    (.store (.op .add [.var .local (ofString "path"),
        .panop .mul [.var .local (ofString "depth"), .const (BitVec.ofNat 64 8)]])
      (.var .local (ofString "node"))) none post events at run
  cases run with
  | storeValue dst src write => rfl

end BoundedTableExperiment

#print axioms BoundedTableExperiment.eval_candidateFindLeafGuard
#print axioms BoundedTableExperiment.candidateFindLeafGuard_internal
#print axioms BoundedTableExperiment.candidateFindLeafGuard_skip
#print axioms BoundedTableExperiment.candidateFindLeafPush_preserves_node

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The depth bump changes only the depth local; the node local is untouched. -/
theorem candidateFindLeafBump_preserves_node {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    {node : BitVec 64}
    (run : StatementRun fn s candidateFindLeafBump none post events)
    (nodeLocal : s.locals.lookup (ofString "node") = some (.val (.word node))) :
    post.locals.lookup (ofString "node") = s.locals.lookup (ofString "node") := by
  change StatementRun fn s
    (.assign .local (ofString "depth")
      (.op .add [.var .local (ofString "depth"),.const (BitVec.ofNat 64 1)]))
    none post events at run
  cases run with
  | assignValue expr valid =>
      show (setVarHOLFinite (ofString "depth") _ s).locals.lookup (ofString "node") =
        s.locals.lookup (ofString "node")
      rw [nodeLocal]
      exact lookup_setVar_ne s (ofString "depth") (ofString "node") _ _
        (by decide) nodeLocal

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidateFindLeafBump_preserves_node

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Guard, push and bump preserve the original node; the walk's route stage
starts from a state whose node local is still the input node. -/
theorem candidateFindLeafStep_walk_node {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    {node : BitVec 64}
    (run : StatementRun fn s candidateFindLeafStep none post events)
    (nodeLocal : s.locals.lookup (ofString "node") = some (.val (.word node))) :
    ∃ (afterGuard afterPush afterBump : PanSemStateFiniteExact 64 F)
      (guardEvents pushEvents bumpEvents routeEvents : List WorkEvent),
      events = guardEvents ++ (pushEvents ++ (bumpEvents ++ routeEvents)) ∧
      afterGuard = s ∧
      afterPush.locals.lookup (ofString "node") = some (.val (.word node)) ∧
      afterBump.locals.lookup (ofString "node") = some (.val (.word node)) ∧
      StatementRun fn afterBump candidateFindLeafRoute none post routeEvents := by
  obtain ⟨afterGuard, afterPush, afterBump, guardEvents, pushEvents,
    bumpEvents, routeEvents, eventsEq, guardRun, pushRun, bumpRun, routeRun⟩ :=
    candidateFindLeafStep_trace run
  have hguard := candidateFindLeafGuard_skip guardRun
  have hpush := candidateFindLeafPush_preserves_node pushRun
  have hpushNode :
      afterPush.locals.lookup (ofString "node") = some (.val (.word node)) := by
    rw [hpush, hguard]
    exact nodeLocal
  have hbump := candidateFindLeafBump_preserves_node bumpRun hpushNode
  have hbumpNode :
      afterBump.locals.lookup (ofString "node") = some (.val (.word node)) := by
    rw [hbump]
    exact hpushNode
  exact ⟨afterGuard, afterPush, afterBump, guardEvents, pushEvents,
    bumpEvents, routeEvents, eventsEq, hguard, hpushNode, hbumpNode, routeRun⟩

end BoundedTableExperiment

#print axioms BoundedTableExperiment.candidateFindLeafStep_walk_node
