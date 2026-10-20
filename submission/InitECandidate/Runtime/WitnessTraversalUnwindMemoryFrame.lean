import InitECandidate.Runtime.WitnessTraversalEmptyUnwindPreserved
import InitECandidate.Runtime.WitnessUnwindExtensionAllocationStack
import InitECandidate.Runtime.WitnessUnwindMoreBranchAllocationStack
import InitECandidate.Runtime.WitnessUnwindLastBranchAllocationStack
import InitECandidate.Runtime.WitnessUnwindExtensionDatabaseFrame
import InitECandidate.Runtime.WitnessUnwindBranchDatabaseFrame
import InitECandidate.Runtime.WitnessUnwindScratchChain
import InitECandidate.Runtime.WitnessUnwindBranchSelectedSlot
import InitECandidate.Runtime.WitnessTraversalStateMeasureProgress
import InitECandidate.Runtime.AllocationRoundNoWrap
import InitECandidate.Runtime.WitnessUnwindModeBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- The actual empty, extension, branch-child and final-branch unwind cases
preserve the full concrete invariant, with no additional caller condition. -/
theorem WitnessTraversalState.unwind_memory_frame {F : Type} (layout : WitnessTraversalLayout)
    (s post : PanSemStateFiniteExact 64 F) (scratch heap top mode go : BitVec 64)
    (valid : WitnessTraversalState layout s scratch heap top mode go) (unwind : mode=0)
    (budget : witnessBranchFinishCost layout.inputLimit≤s.clock)
    (run : evaluateHOLFiniteState s decodeWitnessNodeUnwindMode=(none,post)) : ∀watched : BitVec 64,layout.databaseCeiling≤watched.toNat→watched.toNat<layout.dbHeap.toNat→post.memory watched=s.memory watched := by
  by_cases empty : top=0
  · subst top
    have postEq:=witness_unwind_empty_normal_progress s post valid.atTop run
    intro watched lo hi
    rw [postEq];rfl
  obtain ⟨node,atResult,nodeEnvelope,nodeAbove⟩ := valid.delivered unwind
  have nodeAfterFloor : node=0 ∨ layout.persistentFloor≤node.toNat := by
    rcases nodeEnvelope with zero | ⟨lo,hi⟩
    · exact Or.inl zero
    · exact Or.inr lo
  have childBound : node.toNat≤heap.toNat := by
    rcases nodeEnvelope with zero | ⟨lo,hi⟩
    · subst node;simp
    · omega
  have heapBound:=valid.heapBound
  have nodeBound : node.toNat≤33806089496 := childBound.trans heapBound
  have scratchLo:=valid.scratchLower
  have scratchHi:=valid.scratchBound
  have db:=valid.scratchBeforeDatabase
  have floor:=valid.databaseBeforeFloor
  have heapLo:=valid.floorBeforeHeap
  have limit:=valid.inputLimitBound
  have ordered : layout.frame≤scratch := by change layout.frame.toNat≤scratch.toNat;exact scratchLo
  have limit64 : layout.inputLimit+9<2^64 := by omega
  have arena : ∀ a : BitVec 64, layout.frame.toNat≤a.toNat → a.toNat<scratch.toNat → s.memaddrs a := by
    intro a lo hi;exact valid.scratchArena a lo (by omega)
  obtain ⟨topAbove,topPositive,topBeforeScratch⟩ := valid.scratchChain.head_bounds s top layout.scratchUpper scratch.toNat empty
  have atMode : s.locals.lookup (ofString "mode")=some (.val (.word (0#64))) := by
    rw [valid.atMode,unwind];rfl
  have physical := valid.stack.physical s layout.input layout.inputLength heap top layout.persistentFloor scratch.toNat
  cases physical with
  | nil => exact False.elim (empty rfl)
  | @cons _ previous recordAbove record parentOrder tail =>
    obtain ⟨positive,recordBefore,domainRecord,prevCell,array,count,stage,p,n,kind,atStage,atArray,atP,atN,
      recordBeforeTable,tableEnd,table,nibs,branch⟩ := record
    have hashReadable : s.memaddrs (top+80#64) := domainRecord 80 (by decide)
    have stageReadable : s.memaddrs (top+8#64) := domainRecord 8 (by decide)
    cases hashCell : s.memory (top+80#64) with
    | word hash =>
      rcases kind with ⟨one,countTwo⟩ | ⟨two,countSeventeen⟩
      · subst stage
        have afterRecord := nodeAbove.record_geometry s layout.input layout.inputLength top node layout.persistentFloor scratch.toNat empty
        obtain ⟨builtPost,entriesPost,slicesPost,domain,_,codePost,dbPost,heapPost,growth,capped,aligned,scratchSame,frameSame,memory⟩ :=
          witness_unwind_extension_mode_database_frame s post top node hash heap valid.atTop atResult hashReadable hashCell stageReadable atStage
            valid.atHeap heapBound (by omega) afterRecord nodeBound valid.code empty layout.table layout.dbHeap layout.dbArray layout.total
            layout.input layout.inputLength layout.databaseCeiling layout.persistentFloor valid.atDb valid.built valid.entries valid.slices
            valid.tableAboveDatabase valid.arrayAboveDatabase valid.dbHeapBeforeFloor valid.dbArrayEnd (by omega) nodeAfterFloor heapLo run
        exact memory
      · subst stage;subst count
        obtain ⟨br,index,atBranch,atIndex,indexBound,branchFloor,tableBeforeBranch,branchEnd,branchAligned⟩ := branch rfl
        obtain ⟨pointer,length,entry⟩ := table (16#64) (by decide)
        have lengthBound : length.toNat≤layout.inputLimit :=
          (entry.length_bound s array 16 pointer length layout.input layout.inputLength).trans valid.inputBound
        have afterTable : node=0 ∨ array.toNat+272≤node.toNat := by
          rcases nodeAbove.branch_geometry s layout.input layout.inputLength top node array layout.persistentFloor scratch.toNat empty atStage atArray with
            zero | ⟨_,above⟩
          · exact Or.inl zero
          · exact Or.inr above
        have ticks : witnessBranchFinishCost length.toNat≤s.clock := (witness_branch_finish_cost_mono lengthBound).trans budget
        obtain ⟨builtPost,entriesPost,slicesPost,domain,_,codePost,dbPost,scratchPost,framePost,heapSame,memory⟩ :=
          witness_unwind_branch_mode_database_frame s post array pointer length scratch layout.frame top br index hash scratch.toNat layout.inputLimit
          (domainRecord 24 (by decide)) atArray valid.atTop node atResult recordBeforeTable tableBeforeBranch
          (domainRecord 16 (by decide)) atBranch (domainRecord 32 (by decide)) atIndex indexBound (by omega) entry.readable entry.noWrap
          lengthBound limit64 valid.atScratch valid.atFrame valid.code ordered valid.framePositive (Nat.le_refl _) arena
          hashReadable hashCell stageReadable atStage afterTable nodeBound ticks empty
          layout.table layout.dbHeap layout.dbArray layout.total layout.input layout.inputLength layout.databaseCeiling layout.persistentFloor
          valid.atDb valid.built valid.entries valid.slices valid.tableAboveDatabase valid.arrayAboveDatabase valid.dbHeapBeforeFloor valid.dbArrayEnd
          (by omega) nodeAfterFloor (by omega) branchFloor run
        exact memory
#print axioms WitnessTraversalState.unwind_memory_frame
end InitECandidate.Runtime
