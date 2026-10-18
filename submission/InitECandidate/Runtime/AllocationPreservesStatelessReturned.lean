import InitECandidate.Runtime.AllocationDeclarationReach
import InitECandidate.Runtime.StatelessReturnedMemoryFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successful original allocation declaration preserves all decoded
transaction slices while advancing the real heap/global frame. -/
theorem allocation_preserves_stateless_returned {F : Type}
    (source state next : PanSemStateFiniteExact 64 F) (name : MlS)
    (input length offsets structureHeap pointer size : BitVec 64) (value : ValueHOL 64)
    (decoded : StatelessReturned source input length offsets structureHeap value state)
    (allocated : AllocationDeclarationReady state name pointer size next) :
    StatelessReturned source input length offsets structureHeap value next := by
  obtain ⟨_,memory,_,domain,globals,capped,_,aligned⟩ := allocated
  apply decoded.after_memory_frame source state next input length offsets structureHeap value memory domain
  refine ⟨⟨allocationEnd pointer size,?_,capped,aligned⟩,?_⟩
  · rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro key notHeap
    rw [globals]
    simpa [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notHeap] using
      decoded.2.1.2 key notHeap

#print axioms allocation_preserves_stateless_returned
end InitECandidate.Runtime
