import InitECandidate.Runtime.AllocationDeclarationReach
import InitECandidate.Runtime.AllocationFailureNoReturn
import InitECandidate.Runtime.PanLocalCallNormalResult
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A normally completed assignment-form allocator call supplies the same
exact allocation contract as a declaration, without changing caller scope. -/
theorem allocation_assignment_normal {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (argument : ExpHOL 64) (pointer size : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [argument] = some [.val (.word size)])
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (bounded : pointer.toNat ≤ 33806089496)
    (run : evaluateHOLFiniteState state (.call (some (some (.local,name),none)) (ofString "alloc") [argument]) =
      (none,post)) : AllocationDeclarationReady state name pointer size post := by
  have installed : state.code.lookup (ofString "alloc") =
      some ([(ofString "n",.one)],sourceFunctionBody Guest.guestFn_alloc,.one) := by
    rw [code]; exact originalRuntimeCode_allocation_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "alloc") (ofString "n")
    (sourceFunctionBody Guest.guestFn_alloc) size installed
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "n",.val (.word size))
  let entry := callEntryStateHOLFinite state callee
  have atSize : entry.locals.lookup (ofString "n") = some (.val (.word size)) := by
    simp [entry,callee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨value,bodyPost,bodyRun,_,resumed⟩ := evaluate_localCall_normal_result state post name (ofString "alloc")
    .one [argument] [.val (.word size)] (sourceFunctionBody Guest.guestFn_alloc) callee args lookup run
  have request : size ≤ (33806089496 : BitVec 64) - pointer := by
    by_contra rejected
    have tooBig : ((33806089496 : BitVec 64) - pointer).toNat < size.toNat := by
      have bad : ¬ size.toNat ≤ ((33806089496 : BitVec 64) - pointer).toNat :=
        fun le => rejected (BitVec.le_def.mpr le)
      omega
    obtain ⟨result,output,failure,_,noReturn,_⟩ := evaluate_source_alloc_request_failure_no_return
      entry pointer size code heap atSize tooBig
    exact noReturn value ((Prod.mk.inj (failure.symm.trans bodyRun)).1)
  have within := allocationEnd_within_heap pointer size bounded request
  have rounded := allocationEnd_covers pointer size (allocationGuard_sum_bound pointer size bounded request)
  obtain ⟨output,success,_,_,memory,postCode,domain,_,_,globals⟩ :=
    evaluate_source_alloc_success entry pointer size heap atSize request within
  have equal := Prod.mk.inj (success.symm.trans bodyRun)
  have returned : value = .val (.word pointer) := by
    exact (PanSemResultExact.returned.inj (Option.some.inj equal.1)).symm
  have outputEq : output = bodyPost := equal.2
  subst value
  rw [resumed,← outputEq]
  exact ⟨rfl,memory,postCode,domain,globals,within,rounded.1,rounded.2.2⟩

#print axioms allocation_assignment_normal
end InitECandidate.Runtime
