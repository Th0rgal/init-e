import InitECandidate.Runtime.RunAttemptHeadersToParentReach
import InitECandidate.Runtime.WitnessArrayLinkedWindow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Any older linked witness array in the retained window survives actual
header validation, with its allocation bound advanced to the real frontier.
This applies independently to the state and code database records. -/
theorem RunAttemptHeaderValidationFacts.keeps_witness_array {F : Type}
    (s ready : PanSemStateFiniteExact 64 F)
    (si headers headerCount input inputLength scratch frame heap keccakState keccakPad : BitVec 64)
    (ceiling : Nat)
    (facts : RunAttemptHeaderValidationFacts s ready si headers headerCount input inputLength
      scratch frame heap keccakState keccakPad ceiling)
    (first second array count : BitVec 64)
    (linked : WitnessArrayLinked s si first second array count input inputLength heap)
    (firstInside : first.toNat < 88) (secondInside : second.toNat < 88)
    (recordAbove : ceiling ≤ si.toNat) (recordBefore : si.toNat + 88 ≤ heap.toNat)
    (arrayAbove : count.toNat = 0 ∨ ceiling ≤ array.toNat) :
    ∃ finalHeap : BitVec 64,
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
      heap.toNat ≤ finalHeap.toNat ∧ finalHeap.toNat ≤ 33806089496 ∧ finalHeap.toNat % 8 = 0 ∧
      WitnessArrayLinked ready si first second array count input inputLength finalHeap ∧
      (∀ address : BitVec 64, finalHeap.toNat ≤ address.toNat → address.toNat < 33806089496 →
        ready.memaddrs address) := by
  obtain ⟨value,bodyPost,bodyRun,locals,memoryEq,globalsEq,domainEq,codeEq,valueIs,vhLocal,cap,
    ⟨finalHeap,atHeap,monotone,bounded,aligned,bodyArena,arena⟩,
    scratchPost,framePost,statePost,padPost,window,rest⟩ := facts
  have addressNat (offset : BitVec 64) (inside : offset.toNat < 88) :
      (si + offset).toNat = si.toNat + offset.toNat := by
    have top := heap.isLt
    rw [BitVec.toNat_add_of_lt (by omega)]
  refine ⟨finalHeap,atHeap,monotone,bounded,aligned,?_,arena⟩
  rcases arrayAbove with empty | above
  · refine ⟨?_,?_,?_,?_,?_,linked.countBound,Nat.le_trans linked.arrayEnd monotone⟩
    · rw [domainEq]; exact linked.pointerDomain
    · rw [domainEq]; exact linked.countDomain
    · rw [window _ (by rw [addressNat first firstInside]; omega)
        (by rw [addressNat first firstInside]; omega)]
      exact linked.pointerCell
    · rw [window _ (by rw [addressNat second secondInside]; omega)
        (by rw [addressNat second secondInside]; omega)]
      exact linked.countCell
    · intro slot inside
      omega
  · exact linked.after_memory_between s ready si first second array count input inputLength heap finalHeap ceiling
      (by rw [addressNat first firstInside]; omega)
      (by rw [addressNat first firstInside]; omega)
      (by rw [addressNat second secondInside]; omega)
      (by rw [addressNat second secondInside]; omega) above monotone domainEq window

/-- The exact local/global updates between validation and the first database
call preserve the complete witness record and array memory. -/
theorem WitnessArrayLinked.after_run_attempt_database_prefix {F : Type}
    (s : PanSemStateFiniteExact 64 F)
    (si first second array count input length heap headerCount parent hashes : BitVec 64)
    (linked : WitnessArrayLinked s si first second array count input length heap) :
    WitnessArrayLinked
      (setGlobalHOLFinite (ofString "block_hashes_n") (.val (.word headerCount))
        (setGlobalHOLFinite (ofString "block_hashes") (.val (.word hashes))
          (setVarHOLFinite (ofString "parent") (.val (.word parent))
            (setVarHOLFinite (ofString "nh") (.val (.word headerCount)) s))))
      si first second array count input length heap :=
  linked.after_frame s _ si first second array count input length heap rfl rfl

#print axioms RunAttemptHeaderValidationFacts.keeps_witness_array
#print axioms WitnessArrayLinked.after_run_attempt_database_prefix
end InitECandidate.Runtime
