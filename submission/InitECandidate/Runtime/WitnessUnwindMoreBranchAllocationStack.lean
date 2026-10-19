import InitECandidate.Runtime.WitnessUnwindModeMemoryFrame
import InitECandidate.Runtime.WitnessUnwindModeNormalProgress
import InitECandidate.Runtime.WitnessAllocationStackIndex
import InitECandidate.Runtime.WitnessResultBranchExtent
import InitECandidate.Runtime.WitnessTraversalChildCredit
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual whole-mode child advancement retains the saved allocation order
and decreases rank using the next index stored by the real source. -/
theorem witness_unwind_more_branch_allocation_stack {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array pointer length scratch frame top heap index hash : BitVec 64) (ceiling inputLimit : Nat)
    (arrayReadable : s.memaddrs (top+24#64)) (arrayCell : s.memory (top+24#64) = .word array)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (result : BitVec 64)
    (atResult : s.locals.lookup (ofString "result") = some (.val (.word result)))
    (recordBeforeTable : top.toNat+88 ≤ array.toNat)
    (tableBeforeBranch : array.toNat+272 ≤ heap.toNat)
    (branchReadable : s.memaddrs (top+16#64)) (branchCell : s.memory (top+16#64)=.word heap)
    (indexReadable : s.memaddrs (top+32#64)) (indexCell : s.memory (top+32#64)=.word index)
    (beforeLast : index.toNat<15)
    (heapBound : heap.toNat ≤ 33806089496)
    (slice : RlpSliceEntry s array 16 pointer length)
    (inputRange : pointer.toNat+length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit+9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (hashReadable : s.memaddrs (top+80#64)) (hashCell : s.memory (top+80#64)=.word hash)
    (stageReadable : s.memaddrs (top+8#64)) (stageCell : s.memory (top+8#64)=.word (2#64))
    (resultBound : result.toNat ≤ 33806089496)
    (budget : witnessBranchFinishCost length.toNat ≤ s.clock)
    (nonzero : top ≠ 0)
    (input inputLength frontier previous : BitVec 64) (persistentFloor lower : Nat)
    (stack : WitnessAllocationStack s input inputLength frontier persistentFloor lower top)
    (childAbove : WitnessResultAboveStack s input inputLength top result persistentFloor lower)
    (prevCell : s.memory top=.word previous) (topAbove : ceiling≤top.toNat)
    (atMode : s.locals.lookup (ofString "mode")=some (.val (.word (0#64))))
    (run : evaluateHOLFiniteState s decodeWitnessNodeUnwindMode=(none,post)) :
    WitnessAllocationStack post input inputLength frontier persistentFloor lower top ∧
      post.locals.lookup (ofString "top")=some (.val (.word top)) ∧
      post.locals.lookup (ofString "slot")=some (.val (.word (index+1))) ∧
      post.locals.lookup (ofString "mode")=some (.val (.word (2#64))) ∧
      decodeWitnessMeasure (decoderScratchCapacity frame post) top (witnessTraversalChildCredit post top) 3 <
        decodeWitnessMeasure (decoderScratchCapacity frame s) top (witnessTraversalChildCredit s top) 1 := by
  have resultAfterTable : result=0 ∨ array.toNat+272≤result.toNat := by
    rcases childAbove.branch_geometry s input inputLength top result array persistentFloor lower nonzero stageCell arrayCell with
      zero | ⟨recordEnd,tableEnd⟩
    · exact Or.inl zero
    · exact Or.inr tableEnd
  have resultAfterBranch := childAbove.branch_extent s input inputLength top result heap persistentFloor lower nonzero stageCell branchCell
  obtain ⟨scratchPost,framePost,heapPost,memory⟩ := witness_unwind_branch_mode_memory_frame s post array pointer length scratch frame top heap index hash ceiling inputLimit
    arrayReadable arrayCell atTop result atResult recordBeforeTable tableBeforeBranch branchReadable branchCell
    indexReadable indexCell (by omega) heapBound slice inputRange lengthBound limitBound scratchGlobal frameGlobal
    code orderedFrame framePositive scratchBelow arena hashReadable hashCell stageReadable stageCell resultAfterTable
    resultBound budget nonzero run
  have progress := witness_unwind_branch_mode_normal_progress s post array pointer length scratch frame top heap index hash previous ceiling inputLimit
    arrayReadable arrayCell atTop result atResult recordBeforeTable tableBeforeBranch branchReadable branchCell
    indexReadable indexCell (by omega) heapBound slice inputRange lengthBound limitBound scratchGlobal frameGlobal
    code orderedFrame framePositive scratchBelow arena hashReadable hashCell stageReadable stageCell resultAfterTable
    resultBound budget prevCell topAbove nonzero run
  rcases progress with ⟨more,topPost,slotPost,modePost,indexPost,credit⟩ | ⟨last,_⟩
  · have metadata := evaluateHOLFiniteState_metadata s decodeWitnessNodeUnwindMode
    rw [run] at metadata
    have topNat (offset : Nat) (inside : offset<88) : (top+BitVec.ofNat 64 offset).toNat=top.toNat+offset := by
      rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show offset<2^64 by omega)]
      exact Nat.mod_eq_of_lt (by omega)
    have resultNat : (result+(24 : BitVec 64)).toNat=result.toNat+24 := by
      rw [BitVec.toNat_add]
      change (result.toNat+24)%2^64=result.toNat+24
      exact Nat.mod_eq_of_lt (by omega)
    have keptMemory (watched : BitVec 64) (above : ceiling≤watched.toNat) (below : watched.toNat<heap.toNat)
        (notIndex : watched≠top+32) (notOcc : watched≠top+40) : post.memory watched=s.memory watched := by
      apply memory watched above below notIndex notOcc
      rcases resultAfterBranch with zero | afterBranch
      · exact Or.inl zero
      · apply Or.inr
        intro same
        have equal := congrArg BitVec.toNat same
        rw [resultNat] at equal
        omega
    have nextNat : (index+1).toNat=index.toNat+1 := by
      rw [BitVec.toNat_add_of_lt (by change index.toNat+1<2^64; omega)]; rfl
    have retained := stack.after_branch_index s post input inputLength frontier frontier top heap (index+1) persistentFloor lower
      nonzero stageCell branchCell (Nat.le_refl _) metadata.2.1 (by rw [nextNat]; omega) indexPost (by
        intro offset inside notIndex notOcc notHash
        apply keptMemory
        · rw [topNat offset inside]; omega
        · rw [topNat offset inside]; omega
        · intro same
          have equal := congrArg BitVec.toNat same
          change (top+BitVec.ofNat 64 offset).toNat=(top+BitVec.ofNat 64 32).toNat at equal
          rw [topNat offset inside,topNat 32 (by decide)] at equal
          omega
        · intro same
          have equal := congrArg BitVec.toNat same
          change (top+BitVec.ofNat 64 offset).toNat=(top+BitVec.ofNat 64 40).toNat at equal
          rw [topNat offset inside,topNat 40 (by decide)] at equal
          omega) (by
        intro watched above below
        apply keptMemory watched (by omega) below
        · intro same
          have equal := congrArg BitVec.toNat same
          change watched.toNat=(top+BitVec.ofNat 64 32).toNat at equal
          rw [topNat 32 (by decide)] at equal
          omega
        · intro same
          have equal := congrArg BitVec.toNat same
          change watched.toNat=(top+BitVec.ofNat 64 40).toNat at equal
          rw [topNat 40 (by decide)] at equal
          omega)
    have stageFrame : post.memory (top+8)=s.memory (top+8) := by
      apply keptMemory
      · change ceiling≤(top+BitVec.ofNat 64 8).toNat; rw [topNat 8 (by decide)]; omega
      · change (top+BitVec.ofNat 64 8).toNat<heap.toNat; rw [topNat 8 (by decide)]; omega
      · intro same
        have impossible : (8 : BitVec 64)=32 := by simpa using same
        exact (by decide : (8 : BitVec 64)≠32) impossible
      · intro same
        have impossible : (8 : BitVec 64)=40 := by simpa using same
        exact (by decide : (8 : BitVec 64)≠40) impossible
    have capacity : decoderScratchCapacity frame post=decoderScratchCapacity frame s := by
      simp only [decoderScratchCapacity,scratchPost,scratchGlobal]
    have oldCredit := witnessTraversalChildCredit_branch s top index nonzero stageCell indexCell
    have newCredit := witnessTraversalChildCredit_branch post top (index+1) nonzero (stageFrame.trans stageCell) indexPost
    refine ⟨retained,topPost,slotPost,modePost,?_⟩
    rw [capacity]
    apply decodeWitnessMeasure_child
    · rw [oldCredit,newCredit]; exact credit
    · decide
  · have sameNat := congrArg BitVec.toNat last
    change index.toNat=15 at sameNat
    omega

#print axioms witness_unwind_more_branch_allocation_stack
end InitECandidate.Runtime
