import InitECandidate.Runtime.WitnessTraversalInvariant
import InitECandidate.Runtime.WitnessDecodeModeBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
/-- Actual decode-mode runtime bound derived from the concrete loop-state
invariant. No successful execution or allocation-room premise is required. -/
theorem WitnessTraversalState.decode_bound {F : Type} (layout : WitnessTraversalLayout)
    (s : PanSemStateFiniteExact 64 F) (scratch heap top mode go : BitVec 64)
    (valid : WitnessTraversalState layout s scratch heap top mode go) (decode : mode=1)
    (budget : decodeStepBodyCost layout.inputLimit+1≤s.clock) :
    RunBounded s decodeWitnessNodeDecodeMode (decodeStepBodyCost layout.inputLimit+1) := by
  obtain ⟨pointer,length,atPointer,atLength,spanLo,spanHi,inputRange,lengthBound⟩ := valid.decodeInput decode
  have limit := valid.inputLimitBound
  have before := valid.inputBeforeFrame
  have scratchLo := valid.scratchLower
  have scratchHi := valid.scratchBound
  have db := valid.scratchBeforeDatabase
  have floor := valid.databaseBeforeFloor
  have heapLo := valid.floorBeforeHeap
  apply runBounded_witness_decode_mode s layout.table pointer length scratch layout.frame heap
    scratch.toNat layout.inputLimit valid.atDb atPointer atLength inputRange
    (lengthBound.trans valid.inputBound) (by omega) valid.atScratch valid.atFrame valid.code
    (by change layout.frame.toNat≤scratch.toNat;exact scratchLo) valid.framePositive (Nat.le_refl _)
    (by intro address lo hi;exact valid.scratchArena address lo (by omega)) budget valid.atHeap valid.heapBound
    (by omega) (by intro address lo hi;exact valid.heapArena address (by omega) hi)
    (Or.inl (by omega)) (by omega) (by omega) limit
#print axioms WitnessTraversalState.decode_bound
end InitECandidate.Runtime
