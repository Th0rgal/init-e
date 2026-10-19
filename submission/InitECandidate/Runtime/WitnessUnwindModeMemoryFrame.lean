import InitECandidate.Runtime.WitnessUnwindExtensionHeapFrame
import InitECandidate.Runtime.WitnessUnwindBranchMemoryFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem witness_unwind_extension_mode_heap_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (top result hash heap : BitVec 64)
    (atTop : s.locals.lookup (ofString "top")=some (.val (.word top)))
    (atResult : s.locals.lookup (ofString "result")=some (.val (.word result)))
    (hashReadable : s.memaddrs (top+80#64)) (hashCell : s.memory (top+80#64)=.word hash)
    (stageReadable : s.memaddrs (top+8#64)) (stageCell : s.memory (top+8#64)=.word (1#64))
    (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496)
    (topBound : top.toNat+88 ≤ 33806089496)
    (resultAfterRecord : result=0 ∨ top.toNat+88 ≤ result.toNat)
    (resultBound : result.toNat ≤ 33806089496)
    (code : s.code=originalRuntimeCode)
    (nonzero : top ≠ 0)
    (run : evaluateHOLFiniteState s decodeWitnessNodeUnwindMode=(none,post)) :
    post.globals.lookup (ofString "heap_ptr")=some (.val (.word (allocationEnd heap 56))) ∧
    heap.toNat≤(allocationEnd heap 56).toNat ∧ (allocationEnd heap 56).toNat≤33806089496 ∧
    (allocationEnd heap 56).toNat%8=0 ∧
    post.globals.lookup (ofString "scratch_ptr")=s.globals.lookup (ofString "scratch_ptr") ∧
    post.globals.lookup (ofString "frame_mem_ptr")=s.globals.lookup (ofString "frame_mem_ptr") ∧
    ∀ watched : BitVec 64, watched.toNat<heap.toNat → result=0 ∨ watched≠result+24 →
      post.memory watched=s.memory watched := by
  have evaluation : evaluateHOLFiniteState s decodeWitnessNodeUnwindMode=evaluateHOLFiniteState s witnessUnwindNonempty := by
    rw [source_witness_unwind_dispatch]
    simp [evaluateHOLFiniteState_ite,evalHOLExact,atTop,Compiler.Encoders.Asm.wordCmpHOL,
      show top ≠ 0#64 from nonzero]
  rw [evaluation] at run
  apply witness_unwind_extension_nonempty_heap_frame s post top result hash heap
  all_goals assumption

theorem witness_unwind_branch_mode_memory_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array pointer length scratch frame top heap index hash : BitVec 64) (ceiling inputLimit : Nat)
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
    (nonzero : top ≠ 0)
    (run : evaluateHOLFiniteState s decodeWitnessNodeUnwindMode=(none,post)) :
    post.globals.lookup (ofString "scratch_ptr")=some (.val (.word scratch)) ∧
    post.globals.lookup (ofString "frame_mem_ptr")=some (.val (.word frame)) ∧
    post.globals.lookup (ofString "heap_ptr")=s.globals.lookup (ofString "heap_ptr") ∧
    ∀ watched : BitVec 64, ceiling≤watched.toNat → watched.toNat<heap.toNat →
      watched≠top+32 → watched≠top+40 → result=0 ∨ watched≠result+24 → post.memory watched=s.memory watched := by
  have evaluation : evaluateHOLFiniteState s decodeWitnessNodeUnwindMode=evaluateHOLFiniteState s witnessUnwindNonempty := by
    rw [source_witness_unwind_dispatch]
    simp [evaluateHOLFiniteState_ite,evalHOLExact,atTop,Compiler.Encoders.Asm.wordCmpHOL,
      show top ≠ 0#64 from nonzero]
  rw [evaluation] at run
  apply witness_unwind_branch_nonempty_memory_frame s post array pointer length scratch frame top heap index hash ceiling inputLimit
  all_goals assumption

#print axioms witness_unwind_extension_mode_heap_frame
#print axioms witness_unwind_branch_mode_memory_frame
end InitECandidate.Runtime
