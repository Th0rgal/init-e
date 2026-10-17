import InitECandidate.Runtime.HashNewPrefixInitialized
import InitECandidate.Runtime.HashNewKeysFailure
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successful header followed by rejected keys allocation gives an actual
constructor-body exceptional exit in three clocks, with both scopes restored. -/
theorem evaluate_htabNew_body_keys_failure {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer keyLength capacity : BitVec 64)
    (code : state.code = originalRuntimeCode) (ticks : 3 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (headerRequest : (72 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (headerFinish : (allocationEnd pointer 72).toNat ≤ 33806089496)
    (keyLocal : state.locals.lookup (ofString "key_len") = some (.val (.word keyLength)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (domain0 : state.memaddrs (pointer + 0)) (domain8 : state.memaddrs (pointer + 8))
    (domain16 : state.memaddrs (pointer + 16)) (domain24 : state.memaddrs (pointer + 24))
    (keysRejected : ((33806089496 : BitVec 64) - allocationEnd pointer 72).toNat < (capacity * allocationEnd 0 keyLength).toNat) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_new)).1 ≠ none ∧
      (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_new)).1 ≠ some .timeOut ∧
      (∀ value, (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_new)).1 ≠ some (.returned value)) ∧
      (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_new)).2.clock = state.clock - 3 := by
  obtain ⟨ready,run,clock,postCode,_,heapNext,_,capAfter,strideAfter⟩ := evaluate_htabNew_prefix_initialized state pointer keyLength capacity code (by omega)
    heap headerRequest headerFinish keyLocal capLocal domain0 domain8 domain16 domain24
  have failure := evaluate_htabNew_keys_allocation_failure ready (allocationEnd pointer 72) (allocationEnd 0 keyLength) capacity
    (postCode.trans code) heapNext strideAfter capAfter keysRejected (by omega)
  have resultEq := congrArg Prod.fst run
  change (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_new)).1 =
    (evaluateHOLFiniteState ready htabNewAfterHeader).1 at resultEq
  have clockEq := congrArg (fun output => output.2.clock) run
  change (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_new)).2.clock =
    (evaluateHOLFiniteState ready htabNewAfterHeader).2.clock at clockEq
  refine ⟨by rw [resultEq]; exact failure.1,by rw [resultEq]; exact failure.2.1,?_,?_⟩
  · intro value
    rw [resultEq]; exact failure.2.2.1 value
  · rw [clockEq,failure.2.2.2,clock]
    omega

#print axioms evaluate_htabNew_body_keys_failure
end InitECandidate.Runtime
