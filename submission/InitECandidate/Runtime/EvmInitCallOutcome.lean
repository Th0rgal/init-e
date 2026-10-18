import InitECandidate.Runtime.EvmInitBodyReturned
import InitECandidate.Runtime.EvmInitCallBound
import InitECandidate.Runtime.PanNoArgsLookup
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Actual original initializer calls are bounded in every outcome, and normal
continuation has the exact persistent allocation map and 216-byte heap advance. -/
theorem evaluate_evmInit_call_outcome {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer oldTopic oldSystem oldNull oldEmpty oldKey oldHeader : BitVec 64)
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (topicSlot : state.globals.lookup (ofString "transfer_topic") = some (.val (.word oldTopic)))
    (systemSlot : state.globals.lookup (ofString "vm_system_address") = some (.val (.word oldSystem)))
    (nullSlot : state.globals.lookup (ofString "null_address") = some (.val (.word oldNull)))
    (emptySlot : state.globals.lookup (ofString "evm_empty") = some (.val (.word oldEmpty)))
    (keySlot : state.globals.lookup (ofString "evm_key_buf") = some (.val (.word oldKey)))
    (headerSlot : state.globals.lookup (ofString "pre_hdr_buf") = some (.val (.word oldHeader)))
    (stateGlobal : state.globals.lookup (ofString "keccak_st") = some (.val (.word 2713714976)))
    (padGlobal : state.globals.lookup (ofString "keccak_pad") = some (.val (.word 2713715176)))
    (aligned : pointer.toNat % 8 = 0) (above : 2713714688 ≤ pointer.toNat)
    (small : pointer.toNat + 216 ≤ 33806089496)
    (arena : ∀ address : BitVec 64, 2713714688 ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (budget : 458 ≤ state.clock) :
    let result := evaluateHOLFiniteState state (.call (some (none,none)) (ofString "evm_init") [])
    state.clock ≤ result.2.clock + 458 ∧ result.2.clock ≤ state.clock ∧ result.1 ≠ some .timeOut ∧
      (result.1 = none → result.2.globals = globalAllocationGlobals state.globals pointer evmInitAllocations ∧
        result.2.locals = state.locals ∧ result.2.code = state.code ∧ result.2.memaddrs = state.memaddrs ∧
        ∃ finalHeap : BitVec 64, result.2.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
          finalHeap.toNat = pointer.toNat + 216) := by
  have bounded := evaluate_evmInit_call_bounded state none [] pointer oldTopic oldSystem oldNull oldEmpty
    code heap topicSlot systemSlot nullSlot emptySlot stateGlobal padGlobal aligned above (by omega) arena budget
  refine ⟨bounded.1,bounded.2.1,bounded.2.2,?_⟩
  intro normal
  have lookup := pan_no_args_lookup state.code.lookup (ofString "evm_init")
    (sourceFunctionBody Guest.guestFn_evm_init) (by rw [code]; exact originalRuntimeCode_evmInit_lookup)
  have nonzero : state.clock ≠ 0 := by omega
  revert normal
  rw [evaluateHOLFiniteState_call]
  simp only [evalListHOLFinite,evalListHOLExact]
  rw [lookup]
  simp only [if_neg nonzero]
  cases run : evaluateHOLFiniteState (callEntryStateHOLFinite state HolFiniteMapExact.empty)
      (sourceFunctionBody Guest.guestFn_evm_init) with
  | mk result post =>
    rcases result with _ | (_ | _ | _ | _ | w | _ | _)
    all_goals first
      | (simp; done)
      | skip
    obtain ⟨globals,finalHeap,heapEnd,heapNat⟩ := evaluate_evmInit_body_returned_globals
      (callEntryStateHOLFinite state HolFiniteMapExact.empty) pointer oldTopic oldSystem oldNull oldEmpty oldKey oldHeader w
      code heap topicSlot systemSlot nullSlot emptySlot keySlot headerSlot stateGlobal padGlobal aligned above small arena
      (by change 457 ≤ state.clock - 1; omega) (by rw [run])
    rw [run] at globals heapEnd
    have metadata := evaluateHOLFiniteState_metadata (callEntryStateHOLFinite state HolFiniteMapExact.empty)
      (sourceFunctionBody Guest.guestFn_evm_init)
    rw [run] at metadata
    dsimp only
    split
    · intro _
      exact ⟨globals,rfl,metadata.1,metadata.2.1,finalHeap,heapEnd,heapNat⟩
    · simp

#print axioms evaluate_evmInit_call_outcome
end InitECandidate.Runtime
