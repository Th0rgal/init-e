import InitECandidate.Runtime.WitnessExtensionConstructorHeapFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem witness_extension_normal_heap_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (heap child : BitVec 64)
    (atResult : s.locals.lookup (ofString "result") = some (.val (.word child)))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496)
    (code : s.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState s witnessUnwindExtension = (none,post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word (allocationEnd heap 56))) ∧
    heap.toNat≤(allocationEnd heap 56).toNat ∧ (allocationEnd heap 56).toNat≤33806089496 ∧
    (allocationEnd heap 56).toNat%8=0 ∧
    ∀ watched : BitVec 64, watched.toNat<heap.toNat → post.memory watched=s.memory watched := by
  rw [source_witness_extension] at run
  obtain ⟨guardPost,guardRun,scopeRun⟩ := witness_extension_sequence_normal_parts s post _ _ run
  have same := mpt_fail_guard_normal_state s guardPost _ 8 code guardRun
  subst guardPost
  rw [source_witness_extension_kind_scope] at scopeRun
  obtain ⟨kind,output,initialized,childRun,postEq⟩ := evaluate_dec_normal_scope s post
    (ofString "ck") .one _ _ scopeRun
  let entered := setVarHOLFinite (ofString "ck") kind s
  obtain ⟨guardPost,guardRun,constructorRun⟩ := witness_extension_sequence_normal_parts entered output _ _ childRun
  have same := mpt_fail_guard_normal_state entered guardPost _ 8 code guardRun
  subst guardPost
  have atResultEntered : entered.locals.lookup (ofString "result") = some (.val (.word child)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "ck" ≠ ofString "result" by decide] using atResult
  obtain ⟨nib,length,args⟩ := witness_extension_constructor_normal_arguments entered output child atResultEntered constructorRun
  have facts := witness_extension_constructor_normal_heap_frame entered output heap nib length child
    args atHeap heapBound code constructorRun
  rw [postEq]
  exact facts

#print axioms witness_extension_normal_heap_frame
end InitECandidate.Runtime
