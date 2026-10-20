import InitECandidate.Runtime.AllocationUniformBound
import InitECandidate.Runtime.ProgBounded
import InitECandidate.Runtime.RunAttemptHeadersSource
import InitECandidate.Runtime.OriginalMptNewCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- The actual two-word constructor tail; failed stores terminate early. -/
def mptNewStores : ProgHOL 64 :=
 match structuralFunctionBody Guest.guestFn_mpt_new with
 | .decCall _ _ _ _ body=>body
 | _=>.skip
/-- The complete original constructor takes at most the allocator body tick
and its call tick. No room, readable-memory, or callee callback is assumed. -/
theorem mpt_new_body_bounded : ProgBounded (sourceFunctionBody Guest.guestFn_mpt_new) 2 := by
 have allocator : FunBounded (ofString "alloc") 1 := by
  refine ⟨[(ofString "n",.one)],sourceFunctionBody Guest.guestFn_alloc,.one,
   originalRuntimeCode_allocation_lookup,?_⟩
  intro F s code budget
  have bound:=evaluate_source_alloc_uniform_bounded s code budget
  exact ⟨bound.1,bound.2.1,bound.2.2.1⟩
 have stores : ProgBounded mptNewStores 0 := ProgBounded.straight _ (by decide_cbv)
 have source : sourceFunctionBody Guest.guestFn_mpt_new=
  .decCall (ofString "m") .one (ofString "alloc") [.const 16] mptNewStores := by
  rw [sourceFunctionBody_eq_structural];rfl
 intro F s code budget
 rw [source]
 exact (ProgBounded.decCall allocator (ofString "m") .one [.const 16] stores) s code budget

theorem mpt_new_fun_bounded : FunBounded (ofString "mpt_new") 2 :=
 ⟨[(ofString "root_node",.one),(ofString "secured",.one)],
 sourceFunctionBody Guest.guestFn_mpt_new,.one,originalRuntimeCode_mptNew_lookup,mpt_new_body_bounded⟩
#print axioms mpt_new_body_bounded
#print axioms mpt_new_fun_bounded
end InitECandidate.Runtime
