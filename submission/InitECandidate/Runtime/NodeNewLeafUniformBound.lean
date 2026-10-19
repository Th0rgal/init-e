import InitECandidate.Runtime.NodeNewLeafBody
import InitECandidate.Runtime.AllocationUniformBound
import InitECandidate.Runtime.ProgBounded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original leaf constructor, including heap rejection and store errors,
needs at most two source ticks with no success or local-type assumptions. -/
theorem node_new_leaf_uniform_bounded : ProgBounded (sourceFunctionBody Guest.guestFn_node_new_leaf) 2 := by
  have allocator : FunBounded (ofString "alloc") 1 := by
    refine ⟨[(ofString "n",.one)],sourceFunctionBody Guest.guestFn_alloc,.one,
      originalRuntimeCode_allocation_lookup,?_⟩
    intro F s code budget
    have bound := evaluate_source_alloc_uniform_bounded s code budget
    exact ⟨bound.1,bound.2.1,bound.2.2.1⟩
  have stores : ProgBounded nodeNewLeafStores 0 :=
    ProgBounded.straight _ (by simp only [nodeNewLeafStores,sourceFunctionBody,
      InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]; rfl)
  intro F s code budget
  rw [source_nodeNewLeaf_body]
  exact (ProgBounded.decCall allocator (ofString "nd") .one [.const 64] stores) s code budget

#print axioms node_new_leaf_uniform_bounded
end InitECandidate.Runtime
