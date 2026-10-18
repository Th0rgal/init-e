import InitECandidate.Runtime.PayloadAllocationFailureBound
import InitECandidate.Runtime.AllocationCall
import InitECandidate.Runtime.AllocationAligned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The successful initial allocation enters the original payload continuation
with pl bound and the heap advanced by136, preserving input memory and metadata. -/
theorem payload_allocation_success_entry {F : Type} (state : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (capacity : heap.toNat + 136 ≤ 33806089496) (aligned : heap.toNat % 8 = 0)
    (nonzero : state.clock ≠ 0) :
    ∃ ready : PanSemStateFiniteExact 64 F,
      ready.clock = state.clock - 1 ∧ ready.memory = state.memory ∧ ready.memaddrs = state.memaddrs ∧
      ready.code = state.code ∧ ready.eshapes = state.eshapes ∧ ready.be = state.be ∧
      ready.locals.lookup (ofString "pl") = some (.val (.word heap)) ∧
      (∀ key, key ≠ ofString "pl" → ready.locals.lookup key = state.locals.lookup key) ∧
      ready.globals = (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word (allocationEnd heap 136))) state).globals ∧
      (allocationEnd heap 136).toNat = heap.toNat + 136 ∧
      evaluateHOLFiniteState state (payloadAt 1) =
        (let output := evaluateHOLFiniteState ready (payloadAt 2)
         (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
           (ofString "pl",state.locals.lookup (ofString "pl")))})) := by
  have endNat : (allocationEnd heap 136).toNat = heap.toNat + 136 :=
    allocationEnd_aligned_toNat heap 136 capacity aligned (by decide)
  obtain ⟨allocated,call,ticks,memory,locals,postCode,domain,shapes,endian,globals,declaration⟩ :=
    evaluate_alloc_call_and_declaration state (.const 136) heap 136 (by rfl) code nonzero heapGlobal
      (allocationGuard_of_sum_bound heap 136 capacity) (by rw [endNat]; exact capacity)
  let ready := setVarHOLFinite (ofString "pl") (.val (.word heap)) allocated
  refine ⟨ready,ticks,memory,domain,postCode,shapes,endian,?_,?_,globals,endNat,?_⟩
  · simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro key different
    simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
  · rw [source_payload_allocation]
    exact declaration (ofString "pl") (payloadAt 2)

#print axioms payload_allocation_success_entry
end InitECandidate.Runtime
