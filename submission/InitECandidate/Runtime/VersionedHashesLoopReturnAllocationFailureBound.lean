import InitECandidate.Runtime.VersionedHashesLoopAllocationFailureBound
import InitECandidate.Runtime.VersionedHashesLoopReturnBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_versioned_hashes_loop_return_allocation_failure_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (request : ((33806089496 : BitVec 64) - heap).toNat < 400) (budget : 5 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (versionedHashesAt 7)
    state.clock ≤ evaluated.2.clock + 5 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  have bounded := evaluate_versioned_hashes_loop_allocation_failure_bounded state heap code heapGlobal request budget
  rw [source_versioned_hashes_loop_return]
  exact evaluate_sequence_straight_bounded state versionedHashesLoop versionedHashesReturnTail 5 bounded (by rfl)

#print axioms evaluate_versioned_hashes_loop_return_allocation_failure_bounded
end InitECandidate.Runtime
