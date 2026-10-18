import InitECandidate.Runtime.EvmInitCallBound
import InitECandidate.Runtime.AlignedCellDomains
import InitECandidate.Runtime.MemzeroAlignedCallCells
import InitECandidate.Runtime.KeccakShortCallBoundCells
import InitECandidate.Runtime.EvmInitBodyBoundCells
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
theorem evaluate_evmInit_call_bounded_cells {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64))
    (pointer oldTopic oldSystem oldNull oldEmpty : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (topicSlot : state.globals.lookup (ofString "transfer_topic") = some (.val (.word oldTopic)))
    (systemSlot : state.globals.lookup (ofString "vm_system_address") = some (.val (.word oldSystem)))
    (nullSlot : state.globals.lookup (ofString "null_address") = some (.val (.word oldNull)))
    (emptySlot : state.globals.lookup (ofString "evm_empty") = some (.val (.word oldEmpty)))
    (stateGlobal : state.globals.lookup (ofString "keccak_st") = some (.val (.word 2713714976)))
    (padGlobal : state.globals.lookup (ofString "keccak_pad") = some (.val (.word 2713715176)))
    (aligned : pointer.toNat % 8 = 0) (above : 2713714688 ≤ pointer.toNat)
    (small : pointer.toNat + 88 ≤ 33806089496)
    (arena : ∀ address : BitVec 64, address.toNat % 8 = 0 → 2713714688 ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (budget : 458 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state
      (.call (some (destination,none)) (ofString "evm_init") arguments)
    state.clock ≤ evaluated.2.clock + 458 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  apply evaluate_uniformCallee_call_bounded state (ofString "evm_init") destination arguments 457 budget
  intro values body locals returnShape found
  have same := lookupCodeHOLFinite_installed_body state.code.lookup (ofString "evm_init") []
    (sourceFunctionBody Guest.guestFn_evm_init) body .one returnShape values locals
    (by rw [code]; exact originalRuntimeCode_evmInit_lookup) found
  subst same
  exact evaluate_evmInit_body_bounded_cells (callEntryStateHOLFinite state locals)
    pointer oldTopic oldSystem oldNull oldEmpty code heap topicSlot systemSlot nullSlot emptySlot stateGlobal padGlobal
    aligned above small arena (by change 457 ≤ state.clock - 1; omega)

#print axioms evaluate_evmInit_call_bounded_cells
end InitECandidate.Runtime
