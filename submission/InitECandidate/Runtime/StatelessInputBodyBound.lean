import InitECandidate.Runtime.StatelessAt22InputBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def statelessInputBound (length : BitVec 64) : Nat := sszSplitBound length + length.toNat + 542

/-- The complete original stateless-input decoder uses at most
2*floor(inputLength/4)+inputLength+544 source clocks. This covers rejection,
unreadable input, inaccessible stores, and heap exhaustion. -/
theorem evaluate_stateless_input_body_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length heapPointer offsets : BitVec 64)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (aligned : heapPointer.toNat % 8 = 0)
    (scratchBelow : offsets.toNat + 32 ≤ heapPointer.toNat)
    (inputFits : pointer.toNat + length.toNat < 2 ^ 64)
    (domain0 : state.memaddrs (offsets + 0)) (domain8 : state.memaddrs (offsets + 8))
    (domain16 : state.memaddrs (offsets + 16)) (domain24 : state.memaddrs (offsets + 24))
    (heapArena : ∀ address : BitVec 64, heapPointer.toNat ≤ address.toNat →
      address.toNat < 33806089496 → state.memaddrs address)
    (code : state.code = originalRuntimeCode) (budget : statelessInputBound length ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_stateless_input)
    state.clock ≤ evaluated.2.clock + statelessInputBound length ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  change state.clock ≤ (evaluateHOLFiniteState state (statelessAt 0)).2.clock + statelessInputBound length ∧
    (evaluateHOLFiniteState state (statelessAt 0)).2.clock ≤ state.clock ∧
    (evaluateHOLFiniteState state (statelessAt 0)).1 ≠ some .timeOut
  rcases evaluate_stateless_at22 state pointer length heapPointer offsets code atPointer atLength atOffsets heap heapBound with
    ⟨entry,valid,consumed,remaining,scope⟩ | aborted
  · have tail := evaluate_stateless_at22_input_bounded state entry pointer length heapPointer offsets valid
      atOffsets heapBound aligned scratchBelow inputFits domain0 domain8 domain16 domain24 heapArena code
      (by unfold statelessInputBound at budget; omega)
    have result := scope.1
    have clock := scope.2.1
    refine ⟨?_,?_,?_⟩
    · have spent := tail.1
      unfold statelessInputBound
      omega
    · have kept := tail.2.1
      omega
    · rw [result]
      exact tail.2.2
  · obtain ⟨result,ran,_,consumed,remaining,nt⟩ := aborted
    refine ⟨?_,remaining,?_⟩
    · unfold statelessInputBound
      omega
    · intro timedOut
      exact nt (by unfold statelessInputBound at budget; omega) (Option.some.inj (ran.symm.trans timedOut))

#print axioms evaluate_stateless_input_body_bounded
end InitECandidate.Runtime
