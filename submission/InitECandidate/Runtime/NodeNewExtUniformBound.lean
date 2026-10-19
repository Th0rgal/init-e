import InitECandidate.Runtime.NodeNewExtBody
import InitECandidate.Runtime.AllocationUniformBound
import InitECandidate.Runtime.ProgBounded
import InitECandidate.Runtime.OriginalNodeNewExtCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem node_new_ext_uniform_bounded : ProgBounded (sourceFunctionBody Guest.guestFn_node_new_ext) 2 := by
  have allocator : FunBounded (ofString "alloc") 1 := by
    refine ⟨[(ofString "n",.one)],sourceFunctionBody Guest.guestFn_alloc,.one,
      originalRuntimeCode_allocation_lookup,?_⟩
    intro F s code budget
    have bound := evaluate_source_alloc_uniform_bounded s code budget
    exact ⟨bound.1,bound.2.1,bound.2.2.1⟩
  have stores : ProgBounded nodeNewExtStores 0 :=
    ProgBounded.straight _ (by simp only [nodeNewExtStores,sourceFunctionBody,
      InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]; rfl)
  intro F s code budget
  rw [source_nodeNewExt_body]
  exact (ProgBounded.decCall allocator (ofString "nd") .one [.const 56] stores) s code budget

theorem node_new_ext_fun_bounded : FunBounded (ofString "node_new_ext") 2 :=
  ⟨[(ofString "nib",.one),(ofString "nlen",.one),(ofString "child",.one)],
    sourceFunctionBody Guest.guestFn_node_new_ext,.one,originalRuntimeCode_nodeNewExt_lookup,
    node_new_ext_uniform_bounded⟩
#print axioms node_new_ext_uniform_bounded
#print axioms node_new_ext_fun_bounded
end InitECandidate.Runtime
