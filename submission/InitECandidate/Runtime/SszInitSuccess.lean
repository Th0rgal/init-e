import InitECandidate.Runtime.SszInitNormalize
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def sszInitHashPointer (pointer : BitVec 64) : BitVec 64 :=
  allocationEnd (allocationEnd pointer 32) 64

/-- Successful first SSZ initialization, including all 256 original literal
stores. Its allocated offset buffer and final heap are exposed to the caller. -/
theorem evaluate_sszInit_body_success {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (zero : state.globals.lookup (ofString "zero_hashes") = some (.val (.word 0)))
    (words : ∀ entry ∈ sszInitAllocations, ∃ word : BitVec 64,
      state.globals.lookup entry.1 = some (.val (.word word)))
    (safe : AllocationPlanSafe pointer (sszInitAllocations.map Prod.snd))
    (domain : ∀ cell ∈ sszInitCells, state.memaddrs (sszInitHashPointer pointer + cell.1))
    (budget : 3 ≤ state.clock) :
    ∃ post : PanSemStateFiniteExact 64 F,
      evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_ssz_init) =
        (some (.returned (.val (.word 0))),post) ∧
      post.clock = state.clock - 3 ∧
      post.memory = memWrites state.memory (sszInitHashPointer pointer) sszInitCells ∧
      post.locals = HolFiniteMapExact.empty ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧
      post.globals = globalAllocationGlobals state.globals pointer sszInitAllocations ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (sszInitHashPointer pointer) 2048))) ∧
      post.globals.lookup (ofString "ssz_offs") = some (.val (.word (allocationEnd pointer 32))) ∧
      post.globals.lookup (ofString "zero_hashes") = some (.val (.word (sszInitHashPointer pointer))) := by
  obtain ⟨ready,prefixRun,clock,memory,_,installed,addresses,globals,finalHeap⟩ :=
    evaluate_globalAllocation_prefix state sszInitAllocations sszInitTable pointer code heap
      (by decide) words safe budget
  have hashes : ready.globals.lookup (ofString "zero_hashes") = some (.val (.word (sszInitHashPointer pointer))) := by
    rw [globals]
    simp [globalAllocationGlobals,sszInitAllocations,sszInitHashPointer,HolFiniteMapExact.lookup_update,FUPDATE]
  have offsets : ready.globals.lookup (ofString "ssz_offs") = some (.val (.word (allocationEnd pointer 32))) := by
    rw [globals]
    simp [globalAllocationGlobals,sszInitAllocations,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "zero_hashes" ≠ ofString "ssz_offs" by decide,
      show ofString "heap_ptr" ≠ ofString "ssz_offs" by decide]
  have stores := evaluate_globalConstantStores ready (ofString "zero_hashes") (sszInitHashPointer pointer)
    sszInitCells (.return (.const 0)) hashes (by intro cell member; rw [addresses]; exact domain cell member)
  let post := emptyLocalsHOLFinite {ready with memory := memWrites ready.memory (sszInitHashPointer pointer) sszInitCells}
  refine ⟨post,?_,clock,?_,rfl,installed,addresses,globals,finalHeap,offsets,hashes⟩
  · rw [evaluate_sszInit_normalized state zero]
    change evaluateHOLFiniteState state (globalAllocationProgram sszInitAllocations sszInitTable) = _
    rw [prefixRun]
    change evaluateHOLFiniteState ready (globalConstantStores (ofString "zero_hashes") sszInitCells (.return (.const 0))) = _
    rw [stores]
    simp [evaluateHOLFiniteState_return,evalHOLExact,shapeOfHOLExact,post]
  · change memWrites ready.memory (sszInitHashPointer pointer) sszInitCells = _
    rw [memory]

#print axioms evaluate_sszInit_body_success
end InitECandidate.Runtime
