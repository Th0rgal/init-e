import ActualLiveTrieInvariant
import CandidateFindLeafStepTrace
import InitECandidate.Runtime.RlpEncodeBytesPrefix
import InitECandidate.Runtime.TwoWordValueShape

namespace BoundedTableExperiment

open InitECandidate.Runtime
open InitECandidate.Runtime.FineCost
open Flapjack
open Flapjack.Pancake.PanLang
open Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 2000000


/-- Node links depend only on the memory map. -/
theorem NodeLinkInv.of_mem_eq {F : Type} {s s' : PanSemStateFiniteExact 64 F}
    {node left right route : BitVec 64} (h : s'.memory = s.memory)
    (inv : NodeLinkInv s node left right route) :
    NodeLinkInv s' node left right route := by
  constructor
  · simpa [h] using inv.leftAt
  · simpa [h] using inv.rightAt
  · simpa [h] using inv.routeAt

/-- Route -> byte -> mask -> child carries the node local to the selected child,
including the scoped route/b/m restores. -/
theorem candidateFindLeafRoute_child_node {F : Type} {fn : MlS}
    {s post : PanSemStateFiniteExact 64 F} {events : List WorkEvent}
    {node left right route : BitVec 64}
    (run : StatementRun fn s candidateFindLeafRoute none post events)
    (inv : NodeLinkInv s node left right route)
    (nodeLocal : s.locals.lookup (ofString "node") = some (.val (.word node)))
    {child : BitVec 64} {cl cr childRoute : BitVec 64}
    (childLink : NodeLinkInv s child cl cr childRoute) :
    ∃ (b m : BitVec 64),
      post.locals.lookup (ofString "node") =
        some (.val (.word (if b &&& m = 0 then left else right))) ∧
      post.memory = s.memory ∧
      s.memaddrs (node + 16) := by
  obtain ⟨routeInitEvents, routeBodyEvents, bodyPostR, eventsR, routeInit,
    postEqR, byteRun, routeDom⟩ :=
    candidateFindLeafRoute_route run inv nodeLocal
  obtain ⟨byteVal, byteInitEvents, byteBodyEvents, bodyPostB, eventsB, byteInit,
    byteShape, postEqB, maskRun⟩ := candidateFindLeafByte_dec_split byteRun
  obtain ⟨maskVal, maskInitEvents, maskBodyEvents, bodyPostM, eventsM, maskInit,
    maskShape, postEqM, childRun⟩ := candidateFindLeafMask_dec_split maskRun
  have byteShape' : shapeOfHOLExact byteVal = .one :=
    ((shapeEqHOL_eq_true .one (shapeOfHOLExact byteVal)).mp byteShape).symm
  obtain ⟨byteWord, byteEq⟩ := value_word_of_shape_one byteVal byteShape'
  have maskShape' : shapeOfHOLExact maskVal = .one :=
    ((shapeEqHOL_eq_true .one (shapeOfHOLExact maskVal)).mp maskShape).symm
  obtain ⟨maskWord, maskEq⟩ := value_word_of_shape_one maskVal maskShape'
  let s1 := setVarHOLFinite (ofString "route") (.val (.word route)) s
  let s2 := setVarHOLFinite (ofString "b") byteVal s1
  let s3 := setVarHOLFinite (ofString "m") maskVal s2
  have n1 : s1.locals.lookup (ofString "node") = some (.val (.word node)) := by
    rw [show s1 = setVarHOLFinite (ofString "route") (.val (.word route)) s from rfl]
    exact lookup_setVar_ne s (ofString "route") (ofString "node") _ _
      (by decide) nodeLocal
  have n2 : s2.locals.lookup (ofString "node") = some (.val (.word node)) := by
    rw [show s2 = setVarHOLFinite (ofString "b") byteVal s1 from rfl]
    exact lookup_setVar_ne s1 (ofString "b") (ofString "node") _ _
      (by decide) n1
  have n3 : s3.locals.lookup (ofString "node") = some (.val (.word node)) := by
    rw [show s3 = setVarHOLFinite (ofString "m") maskVal s2 from rfl]
    exact lookup_setVar_ne s2 (ofString "m") (ofString "node") _ _
      (by decide) n2
  have bLocal : s3.locals.lookup (ofString "b") = some (.val (.word byteWord)) := by
    rw [show s3 = setVarHOLFinite (ofString "m") maskVal s2 from rfl]
    rw [lookup_setVar_ne s2 (ofString "m") (ofString "b") _ _
      (by decide) (by
        rw [show s2 = setVarHOLFinite (ofString "b") byteVal s1 from rfl]
        simpa [byteEq] using lookup_setVar_eq s1 (ofString "b") byteVal)]
  have mLocal : s3.locals.lookup (ofString "m") = some (.val (.word maskWord)) := by
    rw [show s3 = setVarHOLFinite (ofString "m") maskVal s2 from rfl]
    simpa [maskEq] using lookup_setVar_eq s2 (ofString "m") maskVal
  have inv3 : NodeLinkInv s3 node left right route := by
    show NodeLinkInv (setVarHOLFinite (ofString "m") maskVal s2) node left right route
    exact NodeLinkInv.of_mem_eq (by rfl) inv
  obtain ⟨flag, guardEvents, branchEvents, eventsEq, guard, flagEq, nodeLookup,
    memEq, domRight, domLeft⟩ :=
    candidateFindLeafChild_links childRun inv3 n3 bLocal mLocal
  have hM : bodyPostB.locals.lookup (ofString "node") =
      bodyPostM.locals.lookup (ofString "node") := by
    rw [postEqM]
    exact lookup_resVarEq_ne bodyPostM.locals (ofString "m") (ofString "node") _
      (by decide)
  have hB : bodyPostR.locals.lookup (ofString "node") =
      bodyPostB.locals.lookup (ofString "node") := by
    rw [postEqB]
    exact lookup_resVarEq_ne bodyPostB.locals (ofString "b") (ofString "node") _
      (by decide)
  have hR : post.locals.lookup (ofString "node") =
      bodyPostR.locals.lookup (ofString "node") := by
    rw [postEqR]
    exact lookup_resVarEq_ne bodyPostR.locals (ofString "route") (ofString "node") _
      (by decide)
  refine ⟨byteWord, maskWord, ?_, ?_, routeDom⟩
  · exact hR.trans (hB.trans (hM.trans nodeLookup))
  · have m1 : post.memory = bodyPostR.memory := by rw [postEqR]
    have m2 : bodyPostR.memory = bodyPostB.memory := by rw [postEqB]
    have m3 : bodyPostB.memory = bodyPostM.memory := by rw [postEqM]
    have m4 : bodyPostM.memory = s.memory := by
      simpa [s3, s2, s1, setVarHOLFinite] using memEq
    exact m1.trans (m2.trans (m3.trans m4))

end BoundedTableExperiment

#print axioms BoundedTableExperiment.NodeLinkInv.of_mem_eq
#print axioms BoundedTableExperiment.candidateFindLeafRoute_child_node
