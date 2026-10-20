import InitECandidate.Runtime.WitnessTraversalIterationBound
import InitECandidate.Runtime.WitnessTraversalDecodePreserved
import InitECandidate.Runtime.WitnessTraversalResolvePreserves
import InitECandidate.Runtime.WitnessTraversalUnwindPreserved
import InitECandidate.Runtime.WitnessTraversalModeRank
import InitECandidate.Runtime.WitnessTraversalUnwindRank
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- The exact original mode dispatch preserves the concrete traversal invariant. -/
theorem WitnessTraversalState.iteration_preserves {F : Type} (layout : WitnessTraversalLayout)
    (s post : PanSemStateFiniteExact 64 F) (scratch heap top mode go : BitVec 64)
    (valid : WitnessTraversalState layout s scratch heap top mode go)
    (budget : witnessTraversalIterationCost layout.inputLimit≤s.clock)
    (run : evaluateHOLFiniteState s decodeWitnessNodeIteration=(none,post)) :
    WitnessTraversalInvariant layout post := by
  have ticks := budget
  unfold witnessTraversalIterationCost at ticks
  rcases valid.modes with unwind | decode | resolve
  · have modeLocal := valid.atMode
    rw [unwind] at modeLocal
    have modeRun := (witness_iteration_dispatch_unwind s modeLocal).symm.trans run
    exact valid.unwind_preserves layout s post scratch heap top mode go unwind (by omega) modeRun
  · have modeLocal := valid.atMode
    rw [decode] at modeLocal
    have modeRun := (witness_iteration_dispatch_decode s modeLocal).symm.trans run
    exact valid.decode_preserves layout s post scratch heap top mode go decode (by omega) modeRun
  · have modeLocal := valid.atMode
    rw [resolve] at modeLocal
    have modeRun := (witness_iteration_dispatch_resolve s modeLocal).symm.trans run
    exact valid.resolve_preserves layout s post scratch heap top mode go resolve (by omega) modeRun
#print axioms WitnessTraversalState.iteration_preserves

/-- The exact original mode dispatch decreases the concrete traversal invariant and state rank. -/
theorem WitnessTraversalState.iteration_decreases {F : Type} (layout : WitnessTraversalLayout)
    (s post : PanSemStateFiniteExact 64 F) (scratch heap top mode go : BitVec 64)
    (valid : WitnessTraversalState layout s scratch heap top mode go)
    (running : go=1)
    (budget : witnessTraversalIterationCost layout.inputLimit≤s.clock)
    (run : evaluateHOLFiniteState s decodeWitnessNodeIteration=(none,post)) :
    witnessTraversalStateMeasure layout.frame post<witnessTraversalStateMeasure layout.frame s := by
  have ticks := budget
  unfold witnessTraversalIterationCost at ticks
  have atGo := valid.atGo
  rw [running] at atGo
  rcases valid.modes with unwind | decode | resolve
  · have modeLocal := valid.atMode
    rw [unwind] at modeLocal
    have modeRun := (witness_iteration_dispatch_unwind s modeLocal).symm.trans run
    exact valid.unwind_decreases layout s post scratch heap top mode go unwind (by omega) atGo modeRun
  · have modeLocal := valid.atMode
    rw [decode] at modeLocal
    have modeRun := (witness_iteration_dispatch_decode s modeLocal).symm.trans run
    exact valid.decode_decreases layout s post scratch heap top mode go decode running (by omega) modeRun
  · have modeLocal := valid.atMode
    rw [resolve] at modeLocal
    have modeRun := (witness_iteration_dispatch_resolve s modeLocal).symm.trans run
    exact valid.resolve_decreases layout s post scratch heap top mode go resolve running (by omega) modeRun
#print axioms WitnessTraversalState.iteration_decreases
end InitECandidate.Runtime
