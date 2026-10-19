import InitECandidate.Runtime.WitnessTraversalInvariant
import InitECandidate.Runtime.WitnessUnwindModeBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
/-- The concrete traversal invariant bounds every actual unwind outcome,
including failed accesses, guards and allocators. No normal run is assumed. -/
theorem WitnessTraversalState.unwind_bound {F : Type} (layout : WitnessTraversalLayout)
    (s : PanSemStateFiniteExact 64 F) (scratch heap top mode go : BitVec 64)
    (valid : WitnessTraversalState layout s scratch heap top mode go) (unwind : mode=0)
    (budget : witnessBranchFinishCost layout.inputLimit≤s.clock) :
    RunBounded s decodeWitnessNodeUnwindMode (witnessBranchFinishCost layout.inputLimit) := by
  by_cases empty : top=0
  · subst top
    exact (runBounded_witness_unwind_empty s valid.atTop valid.code).weaken (Nat.zero_le _)
  obtain ⟨node,atResult,nodeEnvelope,nodeAbove⟩ := valid.delivered unwind
  have nodeBound : node.toNat≤33806089496 := by
    rcases nodeEnvelope with zero | ⟨lower,upper⟩
    · subst node;simp
    · have heapBound:=valid.heapBound;omega
  have physical := valid.stack.physical s layout.input layout.inputLength heap top layout.persistentFloor scratch.toNat
  have scratchLo:=valid.scratchLower
  have scratchHi:=valid.scratchBound
  have beforeDatabase:=valid.scratchBeforeDatabase
  have beforeFloor:=valid.databaseBeforeFloor
  have floorBeforeHeap:=valid.floorBeforeHeap
  have heapBound:=valid.heapBound
  have limit:=valid.inputLimitBound
  cases physical with
  | nil => exact False.elim (empty rfl)
  | cons recordAbove record ordered tail =>
    obtain ⟨positive,recordBefore,domain,prev,array,count,stage,p,n,kind,atStage,atArray,atP,atN,
      recordBeforeTable,tableEnd,table,nibs,branch⟩ := record
    have hashReadable : s.memaddrs (top+80#64) := domain 80 (by decide)
    have stageReadable : s.memaddrs (top+8#64) := domain 8 (by decide)
    cases hashCell : s.memory (top+80#64) with
    | word hash =>
      rcases kind with ⟨stageOne,countTwo⟩ | ⟨stageTwo,countSeventeen⟩
      · subst stage
        have afterRecord := nodeAbove.record_geometry s layout.input layout.inputLength top node layout.persistentFloor scratch.toNat empty
        have bounded := runBounded_witness_unwind_extension_mode s top node hash valid.atTop atResult hashReadable hashCell
          stageReadable atStage (by omega) afterRecord nodeBound empty valid.code
          ((witness_branch_finish_cost_covers_extension layout.inputLimit).trans budget)
        exact bounded.weaken (witness_branch_finish_cost_covers_extension layout.inputLimit)
      · subst stage;subst count
        obtain ⟨br,index,atBranch,atIndex,indexBound,branchFloor,tableBeforeBranch,branchEnd,branchAligned⟩ := branch rfl
        obtain ⟨pointer,length,entry⟩ := table (16#64) (by decide)
        have lengthBound : length.toNat≤layout.inputLimit :=
          (entry.length_bound s array 16 pointer length layout.input layout.inputLength).trans valid.inputBound
        have afterTable : node=0 ∨ array.toNat+272≤node.toNat := by
          rcases nodeAbove.branch_geometry s layout.input layout.inputLength top node array layout.persistentFloor scratch.toNat
            empty atStage atArray with zero | ⟨_,above⟩
          · exact Or.inl zero
          · exact Or.inr above
        have costBound := witness_branch_finish_cost_mono lengthBound
        have bounded := runBounded_witness_unwind_branch_mode s array pointer length scratch layout.frame top br index hash
          scratch.toNat layout.inputLimit (domain 24 (by decide)) atArray valid.atTop node atResult recordBeforeTable tableBeforeBranch
          (domain 16 (by decide)) atBranch (domain 32 (by decide)) atIndex indexBound (by omega) entry.readable entry.noWrap lengthBound
          (by omega) valid.atScratch valid.atFrame valid.code
          (by change layout.frame.toNat≤scratch.toNat;exact scratchLo) valid.framePositive (Nat.le_refl _)
          (by intro address lower upper;exact valid.scratchArena address lower (by omega)) hashReadable hashCell stageReadable atStage
          afterTable nodeBound empty (costBound.trans budget)
        exact bounded.weaken costBound
#print axioms WitnessTraversalState.unwind_bound
end InitECandidate.Runtime
