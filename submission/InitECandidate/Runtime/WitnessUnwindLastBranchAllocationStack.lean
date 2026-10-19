import InitECandidate.Runtime.WitnessUnwindModeMemoryFrame
import InitECandidate.Runtime.WitnessUnwindModeNormalProgress
import InitECandidate.Runtime.WitnessAllocationStackPop
import InitECandidate.Runtime.WitnessResultBranchExtent
import InitECandidate.Runtime.WitnessTraversalChildCredit
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual final-child unwind preserves the saved parent stack and its
result separation, restores the real parent link and strictly decreases rank. -/
theorem witness_unwind_last_branch_allocation_stack {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array pointer length scratch frame top heap hash : BitVec 64) (ceiling inputLimit : Nat)
    (arrayReadable : s.memaddrs (top+24#64)) (arrayCell : s.memory (top+24#64) = .word array)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (result : BitVec 64)
    (atResult : s.locals.lookup (ofString "result") = some (.val (.word result)))
    (recordBeforeTable : top.toNat+88 ≤ array.toNat)
    (tableBeforeBranch : array.toNat+272 ≤ heap.toNat)
    (branchReadable : s.memaddrs (top+16#64)) (branchCell : s.memory (top+16#64)=.word heap)
    (indexReadable : s.memaddrs (top+32#64)) (indexCell : s.memory (top+32#64)=.word (15#64))
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
    post.locals.lookup (ofString "top")=some (.val (.word previous)) ∧
      post.locals.lookup (ofString "result")=some (.val (.word heap)) ∧
      post.locals.lookup (ofString "mode")=some (.val (.word (0#64))) ∧
      WitnessAllocationStack post input inputLength frontier persistentFloor lower previous ∧
      WitnessResultAboveStack post input inputLength previous heap persistentFloor lower ∧
      decodeWitnessMeasure (decoderScratchCapacity frame post) previous (witnessTraversalChildCredit post previous) 1 <
        decodeWitnessMeasure (decoderScratchCapacity frame s) top (witnessTraversalChildCredit s top) 1 := by
  have resultAfterTable : result=0 ∨ array.toNat+272≤result.toNat := by
    rcases childAbove.branch_geometry s input inputLength top result array persistentFloor lower nonzero stageCell arrayCell with
      zero | ⟨recordEnd,tableEnd⟩
    · exact Or.inl zero
    · exact Or.inr tableEnd
  have resultAfterBranch := childAbove.branch_extent s input inputLength top result heap persistentFloor lower nonzero stageCell branchCell
  obtain ⟨scratchPost,framePost,heapPost,memory⟩ := witness_unwind_branch_mode_memory_frame s post array pointer length scratch frame top heap (15#64) hash ceiling inputLimit
    arrayReadable arrayCell atTop result atResult recordBeforeTable tableBeforeBranch branchReadable branchCell
    indexReadable indexCell (by decide) heapBound slice inputRange lengthBound limitBound scratchGlobal frameGlobal
    code orderedFrame framePositive scratchBelow arena hashReadable hashCell stageReadable stageCell resultAfterTable
    resultBound budget nonzero run
  have progress := witness_unwind_branch_mode_normal_progress s post array pointer length scratch frame top heap (15#64) hash previous ceiling inputLimit
    arrayReadable arrayCell atTop result atResult recordBeforeTable tableBeforeBranch branchReadable branchCell
    indexReadable indexCell (by decide) heapBound slice inputRange lengthBound limitBound scratchGlobal frameGlobal
    code orderedFrame framePositive scratchBelow arena hashReadable hashCell stageReadable stageCell resultAfterTable
    resultBound budget prevCell topAbove nonzero run
  rcases progress with ⟨impossible,_⟩ | ⟨last,topPost,resultPost,modePost,cellPost⟩
  · exact False.elim ((by decide : ¬(15#64).toNat<15) impossible)
  · have metadata := evaluateHOLFiniteState_metadata s decodeWitnessNodeUnwindMode
    rw [run] at metadata
    have topNat (offset : Nat) (inside : offset<88) : (top+BitVec.ofNat 64 offset).toNat=top.toNat+offset := by
      rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (show offset<2^64 by omega)]
      exact Nat.mod_eq_of_lt (by omega)
    have resultNat : (result+(24 : BitVec 64)).toNat=result.toNat+24 := by
      rw [BitVec.toNat_add]
      change (result.toNat+24)%2^64=result.toNat+24
      exact Nat.mod_eq_of_lt (by omega)
    obtain ⟨parentStack,parentResult⟩ := stack.branch_pop_after_frame s post input inputLength frontier frontier top previous heap
      persistentFloor lower nonzero prevCell stageCell branchCell (Nat.le_refl _) metadata.2.1 (by
        intro watched afterRecord beforeBranch
        apply memory watched (by omega) beforeBranch
        · intro same
          have equal := congrArg BitVec.toNat same
          change watched.toNat=(top+BitVec.ofNat 64 32).toNat at equal
          rw [topNat 32 (by decide)] at equal
          omega
        · intro same
          have equal := congrArg BitVec.toNat same
          change watched.toNat=(top+BitVec.ofNat 64 40).toNat at equal
          rw [topNat 40 (by decide)] at equal
          omega
        · rcases resultAfterBranch with zero | afterBranch
          · exact Or.inl zero
          · apply Or.inr
            intro same
            have equal := congrArg BitVec.toNat same
            rw [resultNat] at equal
            omega)
    have capacity : decoderScratchCapacity frame post=decoderScratchCapacity frame s := by
      simp only [decoderScratchCapacity,scratchPost,scratchGlobal]
    have measure := (stack.physical s input inputLength frontier top persistentFloor lower).pop_measure s
      input inputLength frontier top previous persistentFloor lower (decoderScratchCapacity frame s)
      (witnessTraversalChildCredit s top) (witnessTraversalChildCredit post previous) 1 1 nonzero prevCell
      (witnessTraversalChildCredit_bound post previous) (by decide)
    refine ⟨topPost,resultPost,modePost.trans atMode,parentStack,parentResult,?_⟩
    rw [capacity]
    exact measure

#print axioms witness_unwind_last_branch_allocation_stack
end InitECandidate.Runtime
