import InitECandidate.Runtime.WitnessTraversalDispatch
import InitECandidate.Runtime.WitnessTraversalDecodeBound
import InitECandidate.Runtime.WitnessTraversalResolveBound
import InitECandidate.Runtime.WitnessTraversalUnwindBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
/-- A common cost for every original witness-loop iteration. -/
def witnessTraversalIterationCost (inputLimit : Nat) : Nat :=
  (decodeStepBodyCost inputLimit+1)+(resolveStepBodyCost inputLimit+1)+witnessBranchFinishCost inputLimit
/-- Every outcome of the exact original three-way dispatch fits the same cost.
Mode arguments and readable memory are derived from the concrete invariant. -/
theorem WitnessTraversalState.iteration_bound {F : Type} (layout : WitnessTraversalLayout)
    (s : PanSemStateFiniteExact 64 F) (scratch heap top mode go : BitVec 64)
    (valid : WitnessTraversalState layout s scratch heap top mode go)
    (budget : witnessTraversalIterationCost layout.inputLimit≤s.clock) :
    RunBounded s decodeWitnessNodeIteration (witnessTraversalIterationCost layout.inputLimit) := by
  have ticks := budget
  unfold witnessTraversalIterationCost at ticks
  rcases valid.modes with unwind | decode | resolve
  · have modeLocal := valid.atMode
    rw [unwind] at modeLocal
    have bounded := valid.unwind_bound layout s scratch heap top mode go unwind (by omega)
    unfold RunBounded at bounded ⊢
    rw [witness_iteration_dispatch_unwind s modeLocal]
    exact ⟨by have h:=bounded.1;unfold witnessTraversalIterationCost;omega,bounded.2⟩
  · have modeLocal := valid.atMode
    rw [decode] at modeLocal
    have bounded := valid.decode_bound layout s scratch heap top mode go decode (by omega)
    unfold RunBounded at bounded ⊢
    rw [witness_iteration_dispatch_decode s modeLocal]
    exact ⟨by have h:=bounded.1;unfold witnessTraversalIterationCost;omega,bounded.2⟩
  · have modeLocal := valid.atMode
    rw [resolve] at modeLocal
    obtain ⟨pointer,length,lengthBound,bounded⟩ := valid.resolve_bound layout s scratch heap top mode go resolve (by omega)
    have mono := resolveStepBodyCost_mono length.toNat layout.inputLimit lengthBound
    unfold RunBounded at bounded ⊢
    rw [witness_iteration_dispatch_resolve s modeLocal]
    exact ⟨by have h:=bounded.1;unfold witnessTraversalIterationCost;omega,bounded.2⟩
#print axioms WitnessTraversalState.iteration_bound
end InitECandidate.Runtime
