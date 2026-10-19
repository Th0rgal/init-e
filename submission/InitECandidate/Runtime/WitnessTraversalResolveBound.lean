import InitECandidate.Runtime.WitnessTraversalInvariant
import InitECandidate.Runtime.WitnessResolveModeBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
/-- The invariant supplies the actual selected input slice and all database
and workspace arguments for the original resolver runtime bound. -/
theorem WitnessTraversalState.resolve_bound {F : Type} (layout : WitnessTraversalLayout)
    (s : PanSemStateFiniteExact 64 F) (scratch heap top mode go : BitVec 64)
    (valid : WitnessTraversalState layout s scratch heap top mode go) (resolve : mode=2)
    (budget : resolveStepBodyCost layout.inputLimit+1≤s.clock) :
    ∃ pointer length : BitVec 64, length.toNat≤layout.inputLimit ∧
      RunBounded s decodeWitnessNodeResolveMode (resolveStepBodyCost length.toNat+1) := by
  obtain ⟨array,slot,pointer,length,cell,readable,atSlot,slotBound,entry,lengthBound⟩ :=
    valid.resolve_arguments layout s scratch heap top mode go resolve
  have limit := valid.inputLimitBound
  have scratchLo := valid.scratchLower
  have scratchHi := valid.scratchBound
  have db := valid.scratchBeforeDatabase
  have floor := valid.databaseBeforeFloor
  refine ⟨pointer,length,lengthBound,?_⟩
  exact runBounded_witness_resolve_mode s pointer length scratch layout.frame layout.table layout.dbHeap
    layout.dbArray layout.total layout.input layout.inputLength array slot top scratch.toNat layout.inputLimit
    valid.atTop readable cell atSlot entry.readable valid.atDb entry.noWrap lengthBound (by omega)
    valid.atScratch valid.atFrame valid.code
    (by change layout.frame.toNat≤scratch.toNat;exact scratchLo) valid.framePositive (Nat.le_refl _)
    (by intro address lo hi;exact valid.scratchArena address lo (by omega)) valid.built valid.entries valid.slices
    (by have h:=valid.tableAboveDatabase;omega) (by have h:=valid.arrayAboveDatabase;omega)
    valid.dbArrayEnd (by have h:=resolveStepBodyCost_mono length.toNat layout.inputLimit lengthBound;omega)
#print axioms WitnessTraversalState.resolve_bound
end InitECandidate.Runtime
