import InitECandidate.Runtime.VersionedHashesEntryLoads
import InitECandidate.Runtime.VersionedHashesInitializedAllocationFailureBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- An exhausted initial heap bounds the entire original validation function,
even for malformed locals, unreadable headers, and arbitrary transaction counts. -/
theorem evaluate_versioned_hashes_body_allocation_failure_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (request : ((33806089496 : BitVec 64) - heap).toNat < 400) (budget : 5 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_is_valid_versioned_hashes)
    state.clock ≤ evaluated.2.clock + 5 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  rw [source_versioned_hashes_entry_loads]
  apply evaluate_dec_one_uniform_clock_bounded state _ _ _ 5
  intro payload
  apply evaluate_dec_one_uniform_clock_bounded (setVarHOLFinite (ofString "pl") (.val (.word payload)) state) _ _ _ 5
  intro array
  apply evaluate_dec_one_uniform_clock_bounded (setVarHOLFinite (ofString "txs") (.val (.word array)) (setVarHOLFinite (ofString "pl") (.val (.word payload)) state)) _ _ _ 5
  intro count
  apply evaluate_dec_one_uniform_clock_bounded (setVarHOLFinite (ofString "ntx") (.val (.word count)) (setVarHOLFinite (ofString "txs") (.val (.word array)) (setVarHOLFinite (ofString "pl") (.val (.word payload)) state))) _ _ _ 5
  intro vh
  apply evaluate_dec_one_uniform_clock_bounded (setVarHOLFinite (ofString "vh") (.val (.word vh)) (setVarHOLFinite (ofString "ntx") (.val (.word count)) (setVarHOLFinite (ofString "txs") (.val (.word array)) (setVarHOLFinite (ofString "pl") (.val (.word payload)) state)))) _ _ _ 5
  intro hashCount
  exact evaluate_versioned_hashes_initialized_allocation_failure_bounded
    (versionedHashesLoadedState state payload array count vh hashCount) heap code heapGlobal request budget

#print axioms evaluate_versioned_hashes_body_allocation_failure_bounded
end InitECandidate.Runtime
