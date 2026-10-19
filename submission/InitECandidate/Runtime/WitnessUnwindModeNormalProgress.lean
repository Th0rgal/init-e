import InitECandidate.Runtime.WitnessUnwindExtensionNormalProgress
import InitECandidate.Runtime.WitnessUnwindBranchNormalProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- The original empty-stack unwind stops its loop and changes only go. -/
theorem witness_unwind_empty_normal_progress {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (atTop : s.locals.lookup (ofString "top")=some (.val (.word (0#64))))
    (run : evaluateHOLFiniteState s decodeWitnessNodeUnwindMode=(none,post)) :
    post=setVarHOLFinite (ofString "go") (.val (.word (0#64))) s := by
  have evaluation : evaluateHOLFiniteState s decodeWitnessNodeUnwindMode=
      evaluateHOLFiniteState s (.assign .local (ofString "go") (.const 0)) := by
    rw [source_witness_unwind_dispatch]
    simp [evaluateHOLFiniteState_ite,evalHOLExact,atTop,Compiler.Encoders.Asm.wordCmpHOL]
  rw [evaluation] at run
  obtain ⟨value,evaluated,postEq⟩ := evaluate_local_assign_normal_value s post _ _ run
  have valueEq : value=.val (.word (0#64)) := by simpa [evalHOLExact] using evaluated.symm
  simpa [valueEq] using postEq

theorem witness_unwind_extension_mode_normal_progress {F : Type} (s post : PanSemStateFiniteExact 64 F)
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
    (run : evaluateHOLFiniteState s decodeWitnessNodeUnwindMode=(none,post)) :
    post.locals.lookup (ofString "top")=some (.val (.word prev)) ∧
    post.locals.lookup (ofString "result")=some (.val (.word heap)) ∧
    post.locals.lookup (ofString "mode")=s.locals.lookup (ofString "mode") ∧ post.memory top=s.memory top := by
  have evaluation : evaluateHOLFiniteState s decodeWitnessNodeUnwindMode=evaluateHOLFiniteState s witnessUnwindNonempty := by
    rw [source_witness_unwind_dispatch]
    simp [evaluateHOLFiniteState_ite,evalHOLExact,atTop,Compiler.Encoders.Asm.wordCmpHOL,
      show top ≠ 0#64 from nonzero]
  rw [evaluation] at run
  apply witness_unwind_extension_nonempty_normal_progress s post top result hash heap prev
  all_goals assumption

theorem witness_unwind_branch_mode_normal_progress {F : Type} (s post : PanSemStateFiniteExact 64 F)
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
    (run : evaluateHOLFiniteState s decodeWitnessNodeUnwindMode=(none,post)) :
    (index.toNat<15 ∧ post.locals.lookup (ofString "top")=some (.val (.word top)) ∧
      post.locals.lookup (ofString "slot")=some (.val (.word (index+1))) ∧
      post.locals.lookup (ofString "mode")=some (.val (.word (2#64))) ∧
      post.memory (top+32#64)=.word (index+1) ∧
      16-(index+1).toNat<16-index.toNat) ∨
    (index=15#64 ∧ post.locals.lookup (ofString "top")=some (.val (.word prev)) ∧
      post.locals.lookup (ofString "result")=some (.val (.word heap)) ∧
      post.locals.lookup (ofString "mode")=s.locals.lookup (ofString "mode") ∧ post.memory top=s.memory top) := by
  have evaluation : evaluateHOLFiniteState s decodeWitnessNodeUnwindMode=evaluateHOLFiniteState s witnessUnwindNonempty := by
    rw [source_witness_unwind_dispatch]
    simp [evaluateHOLFiniteState_ite,evalHOLExact,atTop,Compiler.Encoders.Asm.wordCmpHOL,
      show top ≠ 0#64 from nonzero]
  rw [evaluation] at run
  apply witness_unwind_branch_nonempty_normal_progress s post array pointer length scratch frame top heap index hash prev ceiling inputLimit
  all_goals assumption

#print axioms witness_unwind_empty_normal_progress
#print axioms witness_unwind_extension_mode_normal_progress
#print axioms witness_unwind_branch_mode_normal_progress
end InitECandidate.Runtime
