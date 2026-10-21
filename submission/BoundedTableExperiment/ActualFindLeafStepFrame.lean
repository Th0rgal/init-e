import CandidateFindLeafStepTrace
import CandidateFindLeafPush
import InitECandidate.Runtime.RlpPutBeMemoryWindow

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
