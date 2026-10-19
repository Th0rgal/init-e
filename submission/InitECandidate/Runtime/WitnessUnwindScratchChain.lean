import InitECandidate.Runtime.WitnessScratchChainHeadFrame
import InitECandidate.Runtime.WitnessUnwindModeNormalProgress
import InitECandidate.Runtime.WitnessUnwindModeMemoryFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem witness_unwind_extension_mode_scratch_chain {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (top result hash heap prev : BitVec 64)
    (atTop : s.locals.lookup (ofString "top")=some (.val (.word top)))
    (atResult : s.locals.lookup (ofString "result")=some (.val (.word result)))
    (hashReadable : s.memaddrs (top+80#64)) (hashCell : s.memory (top+80#64)=.word hash)
    (stageReadable : s.memaddrs (top+8#64)) (stageCell : s.memory (top+8#64)=.word (1#64))
    (prevCell : s.memory top=.word prev)
    (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (before : top.toNat<heap.toNat) (heapBound : heap.toNat≤33806089496)
    (topBound : top.toNat+88 ≤ 33806089496)
    (resultAfterRecord : result=0 ∨ top.toNat+88 ≤ result.toNat)
    (resultBound : result.toNat ≤ 33806089496)
    (code : s.code=originalRuntimeCode)
    (nonzero : top ≠ 0)
    (scratch frame : BitVec 64) (upper ceiling persistentFloor : Nat)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)))
    (scratchBelow : scratch.toNat≤ceiling)
    (chain : WitnessScratchChain s upper ceiling top)
    (upperBeforeFloor : upper≤persistentFloor) (floorBeforeHeap : persistentFloor≤heap.toNat)
    (resultAfterFloor : result=0 ∨ persistentFloor≤result.toNat)
    (run : evaluateHOLFiniteState s decodeWitnessNodeUnwindMode=(none,post)) :
    post.locals.lookup (ofString "top")=some (.val (.word prev)) ∧
    post.locals.lookup (ofString "result")=some (.val (.word heap)) ∧
    post.locals.lookup (ofString "mode")=s.locals.lookup (ofString "mode") ∧
    post.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)) ∧
    post.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)) ∧
    WitnessScratchChain post upper scratch.toNat prev := by
  obtain ⟨topPost,resultPost,modePost,_⟩ := witness_unwind_extension_mode_normal_progress s post top result hash heap prev
    atTop atResult hashReadable hashCell stageReadable stageCell prevCell atHeap before heapBound topBound
    resultAfterRecord resultBound code nonzero run
  obtain ⟨_,_,_,_,scratchPost,framePost,memory⟩ := witness_unwind_extension_mode_heap_frame s post top result hash heap
    atTop atResult hashReadable hashCell stageReadable stageCell atHeap heapBound topBound resultAfterRecord resultBound code nonzero run
  have resultNat : (result+(24 : BitVec 64)).toNat=result.toNat+24 := by
    rw [BitVec.toNat_add]
    change (result.toNat+24)%2^64=result.toNat+24
    exact Nat.mod_eq_of_lt (by omega)
  have olderFrame (watched : BitVec 64) (above : top.toNat+88≤watched.toNat) (below : watched.toNat<upper) :
      post.memory watched=s.memory watched := by
    apply memory watched (by omega)
    rcases resultAfterFloor with zero | lower
    · exact Or.inl zero
    · apply Or.inr
      intro same
      have equal:=congrArg BitVec.toNat same
      rw [resultNat] at equal;omega
  have popped := chain.pop_after_frame s post top prev upper ceiling nonzero prevCell olderFrame
  exact ⟨topPost,resultPost,modePost,scratchPost.trans scratchGlobal,framePost.trans frameGlobal,
    popped.after_frame post post prev upper ceiling scratch.toNat scratchBelow (by intro w lo hi;rfl)⟩

theorem witness_unwind_branch_mode_scratch_chain {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array pointer length scratch frame top heap index hash prev : BitVec 64) (ceiling inputLimit : Nat)
    (arrayReadable : s.memaddrs (top+24#64)) (arrayCell : s.memory (top+24#64) = .word array)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word top)))
    (result : BitVec 64)
    (atResult : s.locals.lookup (ofString "result") = some (.val (.word result)))
    (recordBeforeTable : top.toNat+88 ≤ array.toNat)
    (tableBeforeBranch : array.toNat+272 ≤ heap.toNat)
    (branchReadable : s.memaddrs (top+16#64)) (branchCell : s.memory (top+16#64)=.word heap)
    (indexReadable : s.memaddrs (top+32#64)) (indexCell : s.memory (top+32#64)=.word index)
    (indexBound : index.toNat < 16)
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
    (upper persistentFloor : Nat) (chain : WitnessScratchChain s upper ceiling top)
    (upperBeforeFloor : upper≤persistentFloor) (floorBeforeBranch : persistentFloor≤heap.toNat)
    (resultAfterFloor : result=0 ∨ persistentFloor≤result.toNat)
    (run : evaluateHOLFiniteState s decodeWitnessNodeUnwindMode=(none,post)) :
    post.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)) ∧
    post.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)) ∧
    ((index.toNat<15 ∧ post.locals.lookup (ofString "top")=some (.val (.word top)) ∧
       post.locals.lookup (ofString "mode")=some (.val (.word (2#64))) ∧
       WitnessScratchChain post upper scratch.toNat top) ∨
     (index=15#64 ∧ post.locals.lookup (ofString "top")=some (.val (.word prev)) ∧
       post.locals.lookup (ofString "mode")=s.locals.lookup (ofString "mode") ∧
       WitnessScratchChain post upper scratch.toNat prev)) := by
  obtain ⟨scratchPost,framePost,_,memory⟩ := witness_unwind_branch_mode_memory_frame s post array pointer length scratch frame top heap index hash
    ceiling inputLimit arrayReadable arrayCell atTop result atResult recordBeforeTable tableBeforeBranch branchReadable branchCell
    indexReadable indexCell indexBound heapBound slice inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame
    framePositive scratchBelow arena hashReadable hashCell stageReadable stageCell resultAfterTable resultBound budget nonzero run
  have progress := witness_unwind_branch_mode_normal_progress s post array pointer length scratch frame top heap index hash prev
    ceiling inputLimit arrayReadable arrayCell atTop result atResult recordBeforeTable tableBeforeBranch branchReadable branchCell
    indexReadable indexCell indexBound heapBound slice inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame
    framePositive scratchBelow arena hashReadable hashCell stageReadable stageCell resultAfterTable resultBound budget prevCell topAbove nonzero run
  have topNat (offset : Nat) (small : offset<88) : (top+BitVec.ofNat 64 offset).toNat=top.toNat+offset := by
    rw [BitVec.toNat_add,BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega : offset<2^64),Nat.mod_eq_of_lt (by omega : top.toNat+offset<2^64)]
  have resultNat : (result+(24 : BitVec 64)).toNat=result.toNat+24 := by
    rw [BitVec.toNat_add]
    change (result.toNat+24)%2^64=result.toNat+24
    exact Nat.mod_eq_of_lt (by omega)
  have kept (watched : BitVec 64) (above : ceiling≤watched.toNat) (below : watched.toNat<upper)
      (notIndex : watched.toNat≠top.toNat+32) (notOcc : watched.toNat≠top.toNat+40) : post.memory watched=s.memory watched := by
    apply memory watched above (by omega)
    · intro same
      have equal:=congrArg BitVec.toNat same
      change watched.toNat=(top+32#64).toNat at equal
      rw [topNat 32 (by decide)] at equal;exact notIndex equal
    · intro same
      have equal:=congrArg BitVec.toNat same
      change watched.toNat=(top+40#64).toNat at equal
      rw [topNat 40 (by decide)] at equal;exact notOcc equal
    · rcases resultAfterFloor with zero | lower
      · exact Or.inl zero
      · apply Or.inr
        intro same
        have equal:=congrArg BitVec.toNat same
        rw [resultNat] at equal;omega
  obtain ⟨_,_,topBefore⟩ := chain.head_bounds s top upper ceiling nonzero
  have headFrame := kept top topAbove (by omega) (by omega) (by omega)
  have olderFrame (watched : BitVec 64) (above : top.toNat+88≤watched.toNat) (below : watched.toNat<upper) :
      post.memory watched=s.memory watched := kept watched (by omega) below (by omega) (by omega)
  refine ⟨scratchPost,framePost,?_⟩
  rcases progress with ⟨more,topPost,_,modePost,_,_⟩ | ⟨last,topPost,_,modePost,_⟩
  · exact Or.inl ⟨more,topPost,modePost,
      chain.after_head_frame s post top upper ceiling scratch.toNat scratchBelow headFrame olderFrame⟩
  · have popped := chain.pop_after_frame s post top prev upper ceiling nonzero prevCell olderFrame
    exact Or.inr ⟨last,topPost,modePost,
      popped.after_frame post post prev upper ceiling scratch.toNat scratchBelow (by intro w lo hi;rfl)⟩

 theorem witness_unwind_empty_mode_scratch_chain {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (scratch frame : BitVec 64) (upper : Nat)
    (atTop : s.locals.lookup (ofString "top")=some (.val (.word (0#64))))
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)))
    (run : evaluateHOLFiniteState s decodeWitnessNodeUnwindMode=(none,post)) :
    post.locals.lookup (ofString "go")=some (.val (.word (0#64))) ∧
    post.locals.lookup (ofString "top")=some (.val (.word (0#64))) ∧
    post.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)) ∧
    post.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)) ∧
    WitnessScratchChain post upper scratch.toNat 0 := by
  have postEq := witness_unwind_empty_normal_progress s post atTop run
  refine ⟨?_,?_,?_,?_,.nil⟩
  · simp [postEq,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · simpa (config := {decide := true}) [postEq,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using atTop
  · rw [postEq];exact scratchGlobal
  · rw [postEq];exact frameGlobal
#print axioms witness_unwind_empty_mode_scratch_chain

#print axioms witness_unwind_extension_mode_scratch_chain
#print axioms witness_unwind_branch_mode_scratch_chain
end InitECandidate.Runtime
