import InitECandidate.Runtime.HashNewBodyUsedPrefix
import InitECandidate.Runtime.HashNewZeroRuntimePrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Runtime termination for a successful constructor plan needs only its
actual allocation guards, rather than a conservative whole-table reserve. -/
theorem evaluate_htabNew_body_safe_runtime {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer keyLength capacity : BitVec 64) (code : state.code = originalRuntimeCode) (ticks : capacity.toNat + 7 ≤ state.clock)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (headerRequest : (72 : BitVec 64) ≤ (33806089496 : BitVec 64) - pointer)
    (headerFinish : (allocationEnd pointer 72).toNat ≤ 33806089496)
    (keysRequest : capacity * allocationEnd 0 keyLength ≤ (33806089496 : BitVec 64) - allocationEnd pointer 72)
    (keysFinish : (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength)).toNat ≤ 33806089496)
    (keyLocal : state.locals.lookup (ofString "key_len") = some (.val (.word keyLength)))
    (capLocal : state.locals.lookup (ofString "cap") = some (.val (.word capacity)))
    (domains : ∀ offset ∈ ([0,8,16,24,32,40] : List Nat), state.memaddrs (pointer + BitVec.ofNat 64 offset))
    (valuesRequest : capacity * 8 ≤ (33806089496 : BitVec 64) - allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength))
    (valuesFinish : (allocationEnd (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength)) (capacity * 8)).toNat ≤ 33806089496)
    (usedRequest : capacity ≤ (33806089496 : BitVec 64) - allocationEnd (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength)) (capacity * 8))
    (usedFinish : (allocationEnd (allocationEnd (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength)) (capacity * 8)) capacity).toNat ≤ 33806089496)
    (orderRequest : capacity * 8 ≤ (33806089496 : BitVec 64) - allocationEnd (allocationEnd (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength)) (capacity * 8)) capacity)
    (orderFinish : (allocationEnd (allocationEnd (allocationEnd (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength)) (capacity * 8)) capacity) (capacity * 8)).toNat ≤ 33806089496)
    (reverseRequest : capacity * 8 ≤ (33806089496 : BitVec 64) - allocationEnd (allocationEnd (allocationEnd (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength)) (capacity * 8)) capacity) (capacity * 8))
    (reverseFinish : (allocationEnd (allocationEnd (allocationEnd (allocationEnd (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength)) (capacity * 8)) capacity) (capacity * 8)) (capacity * 8)).toNat ≤ 33806089496)
    (domain48 : state.memaddrs (pointer + 48)) (domain56 : state.memaddrs (pointer + 56)) (domain64 : state.memaddrs (pointer + 64))
    (wordDomain : ∀ offset : Nat, offset < capacity.toNat → state.memaddrs ((allocationEnd (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength)) (capacity * 8)) + BitVec.ofNat 64 offset))
    (byteDomain : ∀ offset : Nat, offset < capacity.toNat → state.memaddrs (panByteAlignHOL ((allocationEnd (allocationEnd (allocationEnd pointer 72) (capacity * allocationEnd 0 keyLength)) (capacity * 8)) + BitVec.ofNat 64 offset))) :
    let output := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_htab_new);
    output.1 = some (.returned (.val (.word pointer))) ∧
      state.clock ≤ output.2.clock + capacity.toNat + 7 ∧ output.2.clock ≤ state.clock := by
  obtain ⟨ready,resultEq,clockEq,clock,nextCode,domain,nextHeap,tableLocal,capAfter,usedLocal⟩ :=
    evaluate_htabNew_body_used_prefix state pointer keyLength capacity code (by omega) heap
      headerRequest headerFinish keysRequest keysFinish keyLocal capLocal domains valuesRequest valuesFinish usedRequest usedFinish
  have valuesBound := allocationGuard_sum_bound _ _ keysFinish valuesRequest
  have usedAligned := (allocationEnd_covers _ _ valuesBound).2.2
  have usedBound := allocationGuard_sum_bound _ _ valuesFinish usedRequest
  obtain ⟨zeroed,zeroRun,zeroCost,zeroRemaining,zeroLocals,zeroGlobals,zeroCode,zeroDomain,_⟩ :=
    evaluate_htabNew_zero_runtime_prefix ready pointer _ capacity htabNewAfterZero (nextCode.trans code) (by omega)
      usedBound usedAligned tableLocal usedLocal capAfter (by rw [domain]; exact domain48)
      (by simpa only [domain] using wordDomain) (by simpa only [domain] using byteDomain)
  obtain ⟨post,tail,tailClock,_,_,_,_⟩ :=
    evaluate_htabNew_order_tail zeroed _ pointer capacity (zeroCode.trans (nextCode.trans code)) (by omega)
      (by rw [zeroGlobals]; exact nextHeap) ⟨orderRequest,orderFinish,reverseRequest,reverseFinish,reverseFinish⟩
      (by rw [zeroLocals]; exact tableLocal) (by rw [zeroLocals]; exact capAfter)
      (by rw [zeroDomain,domain]; exact domain56) (by rw [zeroDomain,domain]; exact domain64)
  have usedRun : evaluateHOLFiniteState ready htabNewUsedBody = (some (.returned (.val (.word pointer))),post) := by
    rw [source_htabNew_zero_prefix,zeroRun,tail]
  dsimp only
  refine ⟨?_,?_,?_⟩
  · rw [resultEq,usedRun]
  · rw [clockEq,usedRun]
    dsimp only
    omega
  · rw [clockEq,usedRun]
    dsimp only
    omega

#print axioms evaluate_htabNew_body_safe_runtime
end InitECandidate.Runtime
