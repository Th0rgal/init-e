import InitECandidate.Runtime.WitnessSelectedSlot
import InitECandidate.Runtime.WitnessUnwindModeNormalProgress
import InitECandidate.Runtime.WitnessUnwindModeMemoryFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem witness_unwind_branch_more_mode_selected_slot {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array pointer length scratch frame top heap index hash prev : BitVec 64) (ceiling inputLimit : Nat)
    (arrayReadable : s.memaddrs (top+24#64)) (arrayCell : s.memory (top+24#64) = .word array)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (result : BitVec 64)
    (atResult : s.locals.lookup (ofString "result") = some (.val (.word result)))
    (recordBeforeTable : top.toNat+88 ≤ array.toNat)
    (tableBeforeBranch : array.toNat+272 ≤ heap.toNat)
    (branchReadable : s.memaddrs (top+16#64)) (branchCell : s.memory (top+16#64)=.word heap)
    (indexReadable : s.memaddrs (top+32#64)) (indexCell : s.memory (top+32#64)=.word index)
    (beforeLast : index.toNat < 15)
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
    (resultAfterTable : result=0 ∨ array.toNat+272 ≤ result.toNat)
    (resultBound : result.toNat ≤ 33806089496)
    (budget : witnessBranchFinishCost length.toNat ≤ s.clock)
    (prevCell : s.memory top=.word prev) (topAbove : ceiling≤top.toNat)
    (nonzero : top ≠ 0)
    (run : evaluateHOLFiniteState s decodeWitnessNodeUnwindMode=(none,post)) :
    post.locals.lookup (ofString "top")=some (.val (.word top)) ∧
    post.locals.lookup (ofString "mode")=some (.val (.word (2#64))) ∧ WitnessSelectedSlot post top := by
  have progress := witness_unwind_branch_mode_normal_progress s post array pointer length scratch frame top heap index hash prev
    ceiling inputLimit arrayReadable arrayCell atTop result atResult recordBeforeTable tableBeforeBranch branchReadable branchCell
    indexReadable indexCell (by omega) heapBound slice inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame
    framePositive scratchBelow arena hashReadable hashCell stageReadable stageCell resultAfterTable resultBound budget prevCell topAbove nonzero run
  rcases progress with ⟨_,topPost,slotPost,modePost,indexPost,_⟩ | ⟨last,_⟩
  · obtain ⟨_,_,_,memory⟩ := witness_unwind_branch_mode_memory_frame s post array pointer length scratch frame top heap index hash
      ceiling inputLimit arrayReadable arrayCell atTop result atResult recordBeforeTable tableBeforeBranch branchReadable branchCell
      indexReadable indexCell (by omega) heapBound slice inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame
      framePositive scratchBelow arena hashReadable hashCell stageReadable stageCell resultAfterTable resultBound budget nonzero run
    have topNat (offset : Nat) (inside : offset<88) : (top+BitVec.ofNat 64 offset).toNat=top.toNat+offset := by
      rw [BitVec.toNat_add,BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (by omega : offset<2^64),Nat.mod_eq_of_lt (by omega : top.toNat+offset<2^64)]
    have stageKept : post.memory (top+8)=s.memory (top+8) := by
      apply memory
      · change ceiling≤(top+8#64).toNat
        rw [topNat 8 (by decide)];omega
      · change (top+8#64).toNat<heap.toNat
        rw [topNat 8 (by decide)];omega
      · intro same
        have equal:=congrArg BitVec.toNat same
        change (top+8#64).toNat=(top+32#64).toNat at equal
        rw [topNat 8 (by decide),topNat 32 (by decide)] at equal;omega
      · intro same
        have equal:=congrArg BitVec.toNat same
        change (top+8#64).toNat=(top+40#64).toNat at equal
        rw [topNat 8 (by decide),topNat 40 (by decide)] at equal;omega
      · rcases resultAfterTable with zero | lower
        · exact Or.inl zero
        · apply Or.inr
          intro same
          have resultNat : (result+(24 : BitVec 64)).toNat=result.toNat+24 := by
            rw [BitVec.toNat_add]
            change (result.toNat+24)%2^64=result.toNat+24
            exact Nat.mod_eq_of_lt (by omega)
          have equal:=congrArg BitVec.toNat same
          change (top+8#64).toNat=(result+(24 : BitVec 64)).toNat at equal
          rw [topNat 8 (by decide),resultNat] at equal;omega
    have nextNat : (index+1).toNat=index.toNat+1 := by
      rw [BitVec.toNat_add_of_lt (by change index.toNat+1<2^64;omega)]
      rfl
    exact ⟨topPost,modePost,Or.inr ⟨stageKept.trans stageCell,index+1,indexPost,slotPost,by omega⟩⟩
  · have equal:=congrArg BitVec.toNat last
    change index.toNat=15 at equal
    omega

#print axioms witness_unwind_branch_more_mode_selected_slot
end InitECandidate.Runtime
