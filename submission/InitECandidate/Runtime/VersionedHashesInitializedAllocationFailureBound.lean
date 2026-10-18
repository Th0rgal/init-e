import InitECandidate.Runtime.VersionedHashesInitialization
import InitECandidate.Runtime.VersionedHashesLoopReturnAllocationFailureBound
import InitECandidate.Runtime.PanDecUniformClockBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_versioned_hashes_initialized_allocation_failure_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (request : ((33806089496 : BitVec 64) - heap).toNat < 400) (budget : 5 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (versionedHashesAt 5)
    state.clock ≤ evaluated.2.clock + 5 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  rw [source_versioned_hashes_initialization]
  apply evaluate_dec_one_uniform_clock_bounded
  intro cursor
  apply evaluate_dec_one_uniform_clock_bounded (setVarHOLFinite (ofString "k") (.val (.word cursor)) state) _ _ _ 5
  intro index
  exact evaluate_versioned_hashes_loop_return_allocation_failure_bounded
    (setVarHOLFinite (ofString "i") (.val (.word index)) (setVarHOLFinite (ofString "k") (.val (.word cursor)) state))
    heap code heapGlobal request budget

#print axioms evaluate_versioned_hashes_initialized_allocation_failure_bounded
end InitECandidate.Runtime
