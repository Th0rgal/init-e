import InitECandidate.Runtime.WitnessScratchChainHeadFrame
import InitECandidate.Runtime.WitnessTraversalInvariant
import InitECandidate.Runtime.WitnessUnwindStateMeasure
import InitECandidate.Runtime.WitnessUnwindModeBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- Actual normal unwind strictly lowers the single loop-state measure,
with concrete stage/data arguments derived entirely from the invariant. -/
theorem WitnessTraversalState.unwind_decreases {F : Type} (layout : WitnessTraversalLayout)
    (s post : PanSemStateFiniteExact 64 F) (scratch heap top mode go : BitVec 64)
    (valid : WitnessTraversalState layout s scratch heap top mode go) (unwind : mode=0)
    (budget : witnessBranchFinishCost layout.inputLimit≤s.clock)
    (running : s.locals.lookup (ofString "go")=some (.val (.word (1#64))))
    (run : evaluateHOLFiniteState s decodeWitnessNodeUnwindMode=(none,post)) :
    witnessTraversalStateMeasure layout.frame post<witnessTraversalStateMeasure layout.frame s := by
  by_cases empty : top=0
  · subst top
    exact witness_unwind_empty_state_measure_decreases s post layout.frame valid.atTop running run
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
        exact witness_unwind_extension_state_measure_decreases s post layout.input layout.inputLength top previous node hash heap layout.frame
          layout.persistentFloor scratch.toNat valid.stack nodeAbove childBound valid.atTop atResult atMode hashReadable hashCell stageReadable
          atStage prevCell valid.atHeap heapBound valid.code empty running run
      · subst stage;subst count
        obtain ⟨br,index,atBranch,atIndex,indexBound,branchFloor,tableBeforeBranch,branchEnd,branchAligned⟩ := branch rfl
        obtain ⟨pointer,length,entry⟩ := table (16#64) (by decide)
        have lengthBound : length.toNat≤layout.inputLimit :=
          (entry.length_bound s array 16 pointer length layout.input layout.inputLength).trans valid.inputBound
        have ticks : witnessBranchFinishCost length.toNat≤s.clock := (witness_branch_finish_cost_mono lengthBound).trans budget
        by_cases more : index.toNat<15
        · exact witness_unwind_more_branch_state_measure_decreases s post array pointer length scratch layout.frame top br index hash
            scratch.toNat layout.inputLimit (domainRecord 24 (by decide)) atArray valid.atTop node atResult recordBeforeTable tableBeforeBranch
            (domainRecord 16 (by decide)) atBranch (domainRecord 32 (by decide)) atIndex more (by omega) entry.readable entry.noWrap
            lengthBound limit64 valid.atScratch valid.atFrame valid.code ordered valid.framePositive (Nat.le_refl _) arena
            hashReadable hashCell stageReadable atStage nodeBound ticks empty layout.input layout.inputLength heap previous layout.persistentFloor
            scratch.toNat valid.stack nodeAbove prevCell topAbove atMode running run
        · have last : index=15#64 := BitVec.eq_of_toNat_eq (by change index.toNat=15;omega)
          have lastIndex : s.memory (top+32#64)=.word (15#64) := by
            change s.memory (top+32)=.word (15#64)
            rw [atIndex,last]
          exact witness_unwind_last_branch_state_measure_decreases s post array pointer length scratch layout.frame top br hash
            scratch.toNat layout.inputLimit (domainRecord 24 (by decide)) atArray valid.atTop node atResult recordBeforeTable tableBeforeBranch
            (domainRecord 16 (by decide)) atBranch (domainRecord 32 (by decide)) lastIndex (by omega) entry.readable entry.noWrap
            lengthBound limit64 valid.atScratch valid.atFrame valid.code ordered valid.framePositive (Nat.le_refl _) arena
            hashReadable hashCell stageReadable atStage nodeBound ticks empty layout.input layout.inputLength heap previous layout.persistentFloor
            scratch.toNat valid.stack nodeAbove prevCell topAbove atMode running run

#print axioms WitnessTraversalState.unwind_decreases
end InitECandidate.Runtime
