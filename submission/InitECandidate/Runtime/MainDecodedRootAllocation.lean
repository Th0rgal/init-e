import InitECandidate.Runtime.MainRootAllocationReach
import InitECandidate.Runtime.AllocationPreservesStatelessReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The root declaration carries the decoded input into the hashing continuation.
The allocation may instead terminate through the original allocator trap. -/
theorem main_decoded_root_allocation_reaches {F : Type}
    (source state : PanSemStateFiniteExact 64 F)
    (input length offsets structureHeap : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (decoded : StatelessReturned source input length offsets structureHeap
      (.val (.word structureHeap)) state)
    (si : state.locals.lookup (ofString "si") = some (.val (.word structureHeap)))
    (budget : 2 ≤ state.clock) :
    Reaches state (mainAt 21)
      (fun next => ∃ root : BitVec 64,
        AllocationDeclarationReady state (ofString "root") root 32 next ∧
        next.locals.lookup (ofString "root") = some (.val (.word root)) ∧
        next.locals.lookup (ofString "si") = some (.val (.word structureHeap)) ∧
        StatelessReturned source input length offsets structureHeap
          (.val (.word structureHeap)) next) 2 (mainAt 22) := by
  obtain ⟨root,heap,capped,_⟩ := decoded.2.1.1
  apply reaches_mono state (mainAt 21) (mainAt 22)
    (AllocationDeclarationReady state (ofString "root") root 32) _ 2 2 (by omega)
    _ (main_root_allocation_reaches state root code heap capped budget)
  intro next allocated
  refine ⟨root,allocated,?_,?_,?_⟩
  · rw [allocated.1]
    simp [HolFiniteMapExact.lookup_update,FUPDATE]
  · rw [allocated.1]
    simpa [HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "root" ≠ ofString "si" by decide] using si
  · exact allocation_preserves_stateless_returned source state next (ofString "root")
      input length offsets structureHeap root 32 (.val (.word structureHeap)) decoded allocated

#print axioms main_decoded_root_allocation_reaches
end InitECandidate.Runtime
