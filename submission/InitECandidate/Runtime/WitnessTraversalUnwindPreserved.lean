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
theorem WitnessTraversalState.unwind_preserves {F : Type} (layout : WitnessTraversalLayout)
    (s post : PanSemStateFiniteExact 64 F) (scratch heap top mode go : BitVec 64)
    (valid : WitnessTraversalState layout s scratch heap top mode go) (unwind : mode=0)
    (budget : witnessBranchFinishCost layout.inputLimit≤s.clock)
    (run : evaluateHOLFiniteState s decodeWitnessNodeUnwindMode=(none,post)) : WitnessTraversalInvariant layout post := by
  by_cases empty : top=0
  · subst top
    exact valid.empty_unwind_preserves layout s post scratch heap mode go unwind run
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
  have goPost := (witness_unwind_nonempty_mode_go_normal_kept s post top valid.atTop empty run).trans valid.atGo
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
        obtain ⟨topPost,resultPost,modePost,_,stackPost,resultAbove,_⟩ := witness_unwind_extension_allocation_stack s post
          layout.input layout.inputLength top previous node hash heap layout.frame layout.persistentFloor scratch.toNat
          valid.stack nodeAbove childBound valid.atTop atResult atMode hashReadable hashCell stageReadable atStage prevCell
          valid.atHeap heapBound valid.code empty run
        obtain ⟨builtPost,entriesPost,slicesPost,domain,_,codePost,dbPost,heapPost,growth,capped,aligned,scratchSame,frameSame,_⟩ :=
          witness_unwind_extension_mode_database_frame s post top node hash heap valid.atTop atResult hashReadable hashCell stageReadable atStage
            valid.atHeap heapBound (by omega) afterRecord nodeBound valid.code empty layout.table layout.dbHeap layout.dbArray layout.total
            layout.input layout.inputLength layout.databaseCeiling layout.persistentFloor valid.atDb valid.built valid.entries valid.slices
            valid.tableAboveDatabase valid.arrayAboveDatabase valid.dbHeapBeforeFloor valid.dbArrayEnd (by omega) nodeAfterFloor heapLo run
        obtain ⟨_,_,_,scratchPost,framePost,chainPost⟩ := witness_unwind_extension_mode_scratch_chain s post top node hash heap previous
          valid.atTop atResult hashReadable hashCell stageReadable atStage prevCell valid.atHeap (by omega) heapBound (by omega)
          afterRecord nodeBound valid.code empty scratch layout.frame layout.scratchUpper scratch.toNat layout.persistentFloor
          valid.atScratch valid.atFrame (Nat.le_refl _) valid.scratchChain (by omega) heapLo nodeAfterFloor run
        have covers := allocationEnd_covers_noWrap heap (56#64) (by change heap.toNat+56+7<2^64;omega)
        have delivered : ∃ result : BitVec 64, post.locals.lookup (ofString "result")=some (.val (.word result)) ∧
            (result=0 ∨ (layout.persistentFloor≤result.toNat ∧ result.toNat+32≤(allocationEnd heap 56).toNat)) ∧
            WitnessResultAboveStack post layout.input layout.inputLength previous result layout.persistentFloor scratch.toNat :=
          ⟨heap,resultPost,Or.inr ⟨heapLo,by change heap.toNat+56≤(allocationEnd heap 56).toNat at covers;omega⟩,resultAbove⟩
        exact ⟨scratch,allocationEnd heap 56,previous,0,go,
          WitnessTraversalState.after_components layout s post scratch heap top mode go scratch (allocationEnd heap 56) previous 0 go
            valid domain codePost dbPost goPost topPost modePost scratchPost framePost heapPost scratchLo scratchHi valid.scratchAligned growth capped aligned
            builtPost entriesPost slicesPost stackPost chainPost valid.goBits (Or.inl rfl)
            (by intro bad;cases bad) (by intro bad;cases bad) (fun _ => delivered)⟩
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
        obtain ⟨builtPost,entriesPost,slicesPost,domain,_,codePost,dbPost,scratchPost,framePost,heapSame,_⟩ :=
          witness_unwind_branch_mode_database_frame s post array pointer length scratch layout.frame top br index hash scratch.toNat layout.inputLimit
          (domainRecord 24 (by decide)) atArray valid.atTop node atResult recordBeforeTable tableBeforeBranch
          (domainRecord 16 (by decide)) atBranch (domainRecord 32 (by decide)) atIndex indexBound (by omega) entry.readable entry.noWrap
          lengthBound limit64 valid.atScratch valid.atFrame valid.code ordered valid.framePositive (Nat.le_refl _) arena
          hashReadable hashCell stageReadable atStage afterTable nodeBound ticks empty
          layout.table layout.dbHeap layout.dbArray layout.total layout.input layout.inputLength layout.databaseCeiling layout.persistentFloor
          valid.atDb valid.built valid.entries valid.slices valid.tableAboveDatabase valid.arrayAboveDatabase valid.dbHeapBeforeFloor valid.dbArrayEnd
          (by omega) nodeAfterFloor (by omega) branchFloor run
        have heapPost := heapSame.trans valid.atHeap
        obtain ⟨_,_,chainModes⟩ := witness_unwind_branch_mode_scratch_chain s post array pointer length scratch layout.frame top br index hash previous scratch.toNat layout.inputLimit
          (domainRecord 24 (by decide)) atArray valid.atTop node atResult recordBeforeTable tableBeforeBranch
          (domainRecord 16 (by decide)) atBranch (domainRecord 32 (by decide)) atIndex indexBound (by omega) entry.readable entry.noWrap
          lengthBound limit64 valid.atScratch valid.atFrame valid.code ordered valid.framePositive (Nat.le_refl _) arena
          hashReadable hashCell stageReadable atStage afterTable nodeBound ticks prevCell topAbove empty
          layout.scratchUpper layout.persistentFloor valid.scratchChain (by omega) branchFloor nodeAfterFloor run
        by_cases more : index.toNat<15
        · obtain ⟨stackPost,topPost,slotPost,modePost,_⟩ := witness_unwind_more_branch_allocation_stack s post
            array pointer length scratch layout.frame top br index hash scratch.toNat layout.inputLimit
            (domainRecord 24 (by decide)) atArray valid.atTop node atResult recordBeforeTable tableBeforeBranch
            (domainRecord 16 (by decide)) atBranch (domainRecord 32 (by decide)) atIndex more (by omega) entry.readable entry.noWrap
            lengthBound limit64 valid.atScratch valid.atFrame valid.code ordered valid.framePositive (Nat.le_refl _) arena
            hashReadable hashCell stageReadable atStage nodeBound ticks empty layout.input layout.inputLength heap previous
            layout.persistentFloor scratch.toNat valid.stack nodeAbove prevCell topAbove atMode run
          have selected := (witness_unwind_branch_more_mode_selected_slot s post array pointer length scratch layout.frame top br index hash previous
            scratch.toNat layout.inputLimit (domainRecord 24 (by decide)) atArray valid.atTop node atResult recordBeforeTable tableBeforeBranch
            (domainRecord 16 (by decide)) atBranch (domainRecord 32 (by decide)) atIndex more (by omega) entry.readable entry.noWrap
            lengthBound limit64 valid.atScratch valid.atFrame valid.code ordered valid.framePositive (Nat.le_refl _) arena
            hashReadable hashCell stageReadable atStage afterTable nodeBound ticks prevCell topAbove empty run).2.2
          have chainPost : WitnessScratchChain post layout.scratchUpper scratch.toNat top := by
            rcases chainModes with ⟨_,_,_,chain⟩ | ⟨last,_⟩
            · exact chain
            · have same:=congrArg BitVec.toNat last
              change index.toNat=15 at same;omega
          exact ⟨scratch,heap,top,2,go,
            WitnessTraversalState.after_components layout s post scratch heap top mode go scratch heap top 2 go
              valid domain codePost dbPost goPost topPost modePost scratchPost framePost heapPost scratchLo scratchHi valid.scratchAligned (Nat.le_refl _)
              heapBound valid.heapAligned builtPost entriesPost slicesPost stackPost chainPost valid.goBits (Or.inr (Or.inr rfl))
              (by intro bad;cases bad) (fun _ => ⟨empty,selected⟩) (by intro bad;cases bad)⟩
        · have last : index=15#64 := BitVec.eq_of_toNat_eq (by change index.toNat=15;omega)
          have lastIndex : s.memory (top+32#64)=.word (15#64) := by
            change s.memory (top+32)=.word (15#64)
            rw [atIndex,last]
          obtain ⟨topPost,resultPost,modePost,stackPost,resultAbove,_⟩ := witness_unwind_last_branch_allocation_stack s post
            array pointer length scratch layout.frame top br hash scratch.toNat layout.inputLimit
            (domainRecord 24 (by decide)) atArray valid.atTop node atResult recordBeforeTable tableBeforeBranch
            (domainRecord 16 (by decide)) atBranch (domainRecord 32 (by decide)) lastIndex (by omega) entry.readable entry.noWrap
            lengthBound limit64 valid.atScratch valid.atFrame valid.code ordered valid.framePositive (Nat.le_refl _) arena
            hashReadable hashCell stageReadable atStage nodeBound ticks empty layout.input layout.inputLength heap previous
            layout.persistentFloor scratch.toNat valid.stack nodeAbove prevCell topAbove atMode run
          have chainPost : WitnessScratchChain post layout.scratchUpper scratch.toNat previous := by
            rcases chainModes with ⟨impossible,_⟩ | ⟨_,_,_,chain⟩
            · omega
            · exact chain
          have delivered : ∃ result : BitVec 64, post.locals.lookup (ofString "result")=some (.val (.word result)) ∧
              (result=0 ∨ (layout.persistentFloor≤result.toNat ∧ result.toNat+32≤heap.toNat)) ∧
              WitnessResultAboveStack post layout.input layout.inputLength previous result layout.persistentFloor scratch.toNat :=
            ⟨br,resultPost,Or.inr ⟨branchFloor,by omega⟩,resultAbove⟩
          exact ⟨scratch,heap,previous,0,go,
            WitnessTraversalState.after_components layout s post scratch heap top mode go scratch heap previous 0 go
              valid domain codePost dbPost goPost topPost modePost scratchPost framePost heapPost scratchLo scratchHi valid.scratchAligned (Nat.le_refl _)
              heapBound valid.heapAligned builtPost entriesPost slicesPost stackPost chainPost valid.goBits (Or.inl rfl)
              (by intro bad;cases bad) (by intro bad;cases bad) (fun _ => delivered)⟩
#print axioms WitnessTraversalState.unwind_preserves
end InitECandidate.Runtime
