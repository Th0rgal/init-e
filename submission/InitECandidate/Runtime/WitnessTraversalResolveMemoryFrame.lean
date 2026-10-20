import InitECandidate.Runtime.WitnessTraversalInvariant
import InitECandidate.Runtime.WitnessResolveAllocationStack
import InitECandidate.Runtime.WitnessResolveResultAboveStack
import InitECandidate.Runtime.WitnessResolveModeDatabaseFrame
import InitECandidate.Runtime.WitnessResolveScratchChain
import InitECandidate.Runtime.WitnessResolveModeProgress
import InitECandidate.Runtime.WitnessResolveModeStateMeasure
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- Normal execution of the original resolver preserves the concrete traversal
invariant, using its actual selected slot and actual returned control state. -/
theorem WitnessTraversalState.resolve_memory_frame {F : Type} (layout : WitnessTraversalLayout)
    (s post : PanSemStateFiniteExact 64 F) (scratch heap top mode go : BitVec 64)
    (valid : WitnessTraversalState layout s scratch heap top mode go) (resolve : mode=2)
    (budget : resolveStepBodyCost layout.inputLimit+1≤s.clock)
    (run : evaluateHOLFiniteState s decodeWitnessNodeResolveMode=(none,post)) :
    ∀watched : BitVec 64,layout.databaseCeiling≤watched.toNat→watched.toNat<layout.persistentFloor→post.memory watched=s.memory watched := by
  obtain ⟨array,slot,pointer,length,cell,readable,atSlot,slotBound,entry,lengthBound⟩ :=
    valid.resolve_arguments layout s scratch heap top mode go resolve
  have limit := valid.inputLimitBound
  have scratchLo := valid.scratchLower
  have scratchHi := valid.scratchBound
  have db := valid.scratchBeforeDatabase
  have floor := valid.databaseBeforeFloor
  have heapLo := valid.floorBeforeHeap
  have ordered : layout.frame≤scratch := by change layout.frame.toNat≤scratch.toNat;exact scratchLo
  have limit64 : layout.inputLimit+9<2^64 := by omega
  have arena : ∀ a : BitVec 64, layout.frame.toNat≤a.toNat → a.toNat<scratch.toNat → s.memaddrs a := by
    intro a lo hi;exact valid.scratchArena a lo (by omega)
  have tableAbove : scratch.toNat≤layout.table.toNat := by have h:=valid.tableAboveDatabase;omega
  have arrayAbove : scratch.toNat≤layout.dbArray.toNat := by have h:=valid.arrayAboveDatabase;omega
  have spanSize := entry.length_bound s array slot pointer length layout.input layout.inputLength
  have ticks : resolveStepBodyCost length.toNat+1≤s.clock := by
    have h:=resolveStepBodyCost_mono length.toNat layout.inputLimit lengthBound;omega
  obtain ⟨nonempty,selected⟩ := valid.resolveSelector resolve
  obtain ⟨topAbove,topPositive,topBefore⟩ := valid.scratchChain.head_bounds s top layout.scratchUpper scratch.toNat nonempty
  obtain ⟨_,_,nextHeap,heapPost,growth,capped,aligned,memory⟩ := witness_resolve_mode_normal_heap_frame
    s post pointer length scratch layout.frame layout.table layout.dbHeap layout.dbArray layout.total layout.input layout.inputLength array slot top heap scratch.toNat layout.inputLimit
    valid.atHeap valid.heapBound valid.heapAligned valid.atTop readable cell atSlot entry.readable valid.atDb entry.noWrap lengthBound limit64 valid.atScratch valid.atFrame valid.code ordered valid.framePositive (Nat.le_refl _) arena valid.built valid.entries valid.slices tableAbove arrayAbove valid.dbArrayEnd entry.startsWithin entry.endsWithin spanSize ticks run
  intro watched lo hi
  apply memory watched (by omega) (by omega)
  intro equal
  have topNat : (top+80#64).toNat=top.toNat+80 := by
    rw [BitVec.toNat_add];change (top.toNat+80)%(2^64)=top.toNat+80
    apply Nat.mod_eq_of_lt
    have max:=heap.isLt;omega
  have same:=congrArg BitVec.toNat equal
  change watched.toNat=(top+80#64).toNat at same
  rw [topNat] at same
  omega
#print axioms WitnessTraversalState.resolve_memory_frame
end InitECandidate.Runtime
