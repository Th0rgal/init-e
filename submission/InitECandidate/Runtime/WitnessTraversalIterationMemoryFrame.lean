import InitECandidate.Runtime.WitnessTraversalDecodeMemoryFrame
import InitECandidate.Runtime.WitnessTraversalResolveMemoryFrame
import InitECandidate.Runtime.WitnessTraversalUnwindMemoryFrame
import InitECandidate.Runtime.WitnessTraversalIterationBound
import InitECandidate.Runtime.WitnessTraversalDecodePreserved
import InitECandidate.Runtime.WitnessTraversalResolvePreserves
import InitECandidate.Runtime.WitnessTraversalUnwindPreserved
import InitECandidate.Runtime.WitnessTraversalModeRank
import InitECandidate.Runtime.WitnessTraversalUnwindRank
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The exact original mode dispatch preserves the concrete traversal invariant. -/
theorem WitnessTraversalState.iteration_memory_frame {F : Type} (layout : WitnessTraversalLayout)
    (s post : PanSemStateFiniteExact 64 F) (scratch heap top mode go : BitVec 64)
    (valid : WitnessTraversalState layout s scratch heap top mode go)
    (budget : witnessTraversalIterationCost layout.inputLimit≤s.clock)
    (run : evaluateHOLFiniteState s decodeWitnessNodeIteration=(none,post)) :
    ∀watched : BitVec 64,layout.databaseCeiling≤watched.toNat→watched.toNat<layout.dbHeap.toNat→post.memory watched=s.memory watched := by
  have ticks := budget
  unfold witnessTraversalIterationCost at ticks
  rcases valid.modes with unwind | decode | resolve
  · have modeLocal := valid.atMode
    rw [unwind] at modeLocal
    have modeRun := (witness_iteration_dispatch_unwind s modeLocal).symm.trans run
    exact valid.unwind_memory_frame layout s post scratch heap top mode go unwind (by omega) modeRun
  · have modeLocal := valid.atMode
    rw [decode] at modeLocal
    have modeRun := (witness_iteration_dispatch_decode s modeLocal).symm.trans run
    intro watched lo hi
    exact valid.decode_memory_frame layout s post scratch heap top mode go decode (by omega) modeRun watched lo (hi.trans_le valid.dbHeapBeforeFloor)
  · have modeLocal := valid.atMode
    rw [resolve] at modeLocal
    have modeRun := (witness_iteration_dispatch_resolve s modeLocal).symm.trans run
    intro watched lo hi
    exact valid.resolve_memory_frame layout s post scratch heap top mode go resolve (by omega) modeRun watched lo (hi.trans_le valid.dbHeapBeforeFloor)
#print axioms WitnessTraversalState.iteration_memory_frame
end InitECandidate.Runtime
