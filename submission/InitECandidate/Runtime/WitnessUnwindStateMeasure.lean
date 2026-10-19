import InitECandidate.Runtime.WitnessUnwindExtensionAllocationStack
import InitECandidate.Runtime.WitnessUnwindMoreBranchAllocationStack
import InitECandidate.Runtime.WitnessUnwindLastBranchAllocationStack
import InitECandidate.Runtime.WitnessTraversalStateMeasureProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem witness_unwind_extension_state_measure_decreases {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (input inputLength top previous child hash heap frame : BitVec 64) (persistentFloor lower : Nat)
    (stack : WitnessAllocationStack s input inputLength heap persistentFloor lower top)
    (childAbove : WitnessResultAboveStack s input inputLength top child persistentFloor lower)
    (childBound : child.toNat≤heap.toNat)
    (atTop : s.locals.lookup (ofString "top")=some (.val (.word top)))
    (atResult : s.locals.lookup (ofString "result")=some (.val (.word child)))
    (atMode : s.locals.lookup (ofString "mode")=some (.val (.word (0#64))))
    (hashReadable : s.memaddrs (top+80#64)) (hashCell : s.memory (top+80#64)=.word hash)
    (stageReadable : s.memaddrs (top+8#64)) (stageCell : s.memory (top+8#64)=.word (1#64))
    (prevCell : s.memory top=.word previous)
    (atHeap : s.globals.lookup (ofString "heap_ptr")=some (.val (.word heap)))
    (heapBound : heap.toNat≤33806089496) (code : s.code=originalRuntimeCode) (nonempty : top≠0)
    (running : s.locals.lookup (ofString "go")=some (.val (.word (1#64))))
    (run : evaluateHOLFiniteState s decodeWitnessNodeUnwindMode=(none,post)) :
    witnessTraversalStateMeasure frame post<witnessTraversalStateMeasure frame s := by
  obtain ⟨topPost,_,modePost,_,_,_,rank⟩ := witness_unwind_extension_allocation_stack s post input inputLength top previous child hash heap frame persistentFloor lower stack childAbove childBound atTop atResult atMode hashReadable hashCell stageReadable stageCell prevCell atHeap heapBound code nonempty run
  have postRunning := (witness_unwind_nonempty_mode_go_normal_kept s post top atTop nonempty run).trans running
  exact witnessTraversalStateMeasure_decreases_of_running s post frame top previous 1 1
    running postRunning atTop topPost (witnessTraversalModeCredit_delivery s atMode)
    (witnessTraversalModeCredit_delivery post modePost) rank
#print axioms witness_unwind_extension_state_measure_decreases

theorem witness_unwind_more_branch_state_measure_decreases {F : Type} (s post : PanSemStateFiniteExact 64 F)
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
    (running : s.locals.lookup (ofString "go")=some (.val (.word (1#64))))
    (run : evaluateHOLFiniteState s decodeWitnessNodeUnwindMode=(none,post)) :
    witnessTraversalStateMeasure frame post<witnessTraversalStateMeasure frame s := by
  obtain ⟨_,topPost,_,modePost,rank⟩ := witness_unwind_more_branch_allocation_stack s post array pointer length scratch frame top heap index hash ceiling inputLimit arrayReadable arrayCell atTop result atResult recordBeforeTable tableBeforeBranch branchReadable branchCell indexReadable indexCell beforeLast heapBound slice inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena hashReadable hashCell stageReadable stageCell resultBound budget nonzero input inputLength frontier previous persistentFloor lower stack childAbove prevCell topAbove atMode run
  have postRunning := (witness_unwind_nonempty_mode_go_normal_kept s post top atTop nonzero run).trans running
  exact witnessTraversalStateMeasure_decreases_of_running s post frame top top 1 3
    running postRunning atTop topPost (witnessTraversalModeCredit_delivery s atMode)
    (witnessTraversalModeCredit_resolve post modePost) rank
#print axioms witness_unwind_more_branch_state_measure_decreases

theorem witness_unwind_last_branch_state_measure_decreases {F : Type} (s post : PanSemStateFiniteExact 64 F)
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
    (running : s.locals.lookup (ofString "go")=some (.val (.word (1#64))))
    (run : evaluateHOLFiniteState s decodeWitnessNodeUnwindMode=(none,post)) :
    witnessTraversalStateMeasure frame post<witnessTraversalStateMeasure frame s := by
  obtain ⟨topPost,_,modePost,_,_,rank⟩ := witness_unwind_last_branch_allocation_stack s post array pointer length scratch frame top heap hash ceiling inputLimit arrayReadable arrayCell atTop result atResult recordBeforeTable tableBeforeBranch branchReadable branchCell indexReadable indexCell heapBound slice inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena hashReadable hashCell stageReadable stageCell resultBound budget nonzero input inputLength frontier previous persistentFloor lower stack childAbove prevCell topAbove atMode run
  have postRunning := (witness_unwind_nonempty_mode_go_normal_kept s post top atTop nonzero run).trans running
  exact witnessTraversalStateMeasure_decreases_of_running s post frame top previous 1 1
    running postRunning atTop topPost (witnessTraversalModeCredit_delivery s atMode)
    (witnessTraversalModeCredit_delivery post modePost) rank
#print axioms witness_unwind_last_branch_state_measure_decreases
end InitECandidate.Runtime
