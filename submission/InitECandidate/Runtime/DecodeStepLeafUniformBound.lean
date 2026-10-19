import InitECandidate.Runtime.NodeNewLeafUniformBound
import InitECandidate.Runtime.OriginalNodeNewLeafCode
import InitECandidate.Runtime.DecodeStepLeafConstruction
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual leaf construction and metadata stores, including allocator and
memory failures, are bounded without a heap reserve or local-type assumptions. -/
theorem decode_step_leaf_construction_uniform_bounded : ProgBounded decodeStepLeafConstruction 3 := by
  have constructor : FunBounded (ofString "node_new_leaf") 2 :=
    ⟨_,_,_,originalRuntimeCode_nodeNewLeaf_lookup,node_new_leaf_uniform_bounded⟩
  have stores : ProgBounded decodeStepLeafStores 0 := ProgBounded.straight _ (by
    rw [source_decodeStep_leaf_stores]; rfl)
  intro F s code budget
  rw [source_decodeStep_leaf_construction]
  exact (ProgBounded.decCall constructor (ofString "lf") .one _ stores) s code budget

#print axioms decode_step_leaf_construction_uniform_bounded
end InitECandidate.Runtime
