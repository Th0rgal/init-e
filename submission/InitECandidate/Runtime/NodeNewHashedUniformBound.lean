import InitECandidate.Runtime.NodeNewHashedBody
import InitECandidate.Runtime.AllocationUniformBound
import InitECandidate.Runtime.ProgBounded
import InitECandidate.Runtime.OriginalNodeNewHashedCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem node_new_hashed_uniform_bounded : ProgBounded (sourceFunctionBody Guest.guestFn_node_new_hashed) 2 := by
  have allocator : FunBounded (ofString "alloc") 1 := by
    refine ⟨[(ofString "n",.one)],sourceFunctionBody Guest.guestFn_alloc,.one,
      originalRuntimeCode_allocation_lookup,?_⟩
    intro F s code budget
    have bound := evaluate_source_alloc_uniform_bounded s code budget
    exact ⟨bound.1,bound.2.1,bound.2.2.1⟩
  have stores : ProgBounded nodeNewHashedStores 0 :=
    ProgBounded.straight _ (by simp only [nodeNewHashedStores,sourceFunctionBody,
      InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]; rfl)
  intro F s code budget
  rw [source_nodeNewHashed_body]
  exact (ProgBounded.decCall allocator (ofString "nd") .one [.const 32] stores) s code budget

theorem node_new_hashed_fun_bounded : FunBounded (ofString "node_new_hashed") 2 :=
  ⟨[(ofString "hash",.one)],
    sourceFunctionBody Guest.guestFn_node_new_hashed,.one,originalRuntimeCode_nodeNewHashed_lookup,
    node_new_hashed_uniform_bounded⟩
#print axioms node_new_hashed_uniform_bounded
#print axioms node_new_hashed_fun_bounded
end InitECandidate.Runtime
