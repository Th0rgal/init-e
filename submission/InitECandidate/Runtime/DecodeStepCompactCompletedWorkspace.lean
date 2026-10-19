import InitECandidate.Runtime.DecodeStepCompactTableBound
import InitECandidate.Runtime.DecodeStepPathCompletedWorkspace
import InitECandidate.Runtime.ReachesReturnedContinuation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

private theorem remainingBudget {a b initial remaining : Nat}
    (total : a + b ≤ initial) (spent : initial ≤ remaining + a) : b ≤ remaining := by omega

/-- A completed node returned through the actual compact call restores both
workspace pointers; the second slice is retained through the actual callee. -/
theorem decode_step_compact_call_completed_workspace {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (kind pointer length consumed array secondPointer secondLength heap scratch frame : BitVec 64)
    (atItem : s.locals.lookup (ofString "pi") = some
      (.rStruct [.val (.word kind),.val (.word pointer),.val (.word length),.val (.word consumed)]))
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (second : RlpSliceEntry s array 1 secondPointer secondLength)
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (aligned : heap.toNat % 8 = 0)
    (tableBefore : array.toNat + 32 ≤ heap.toNat) (inputBound : length.toNat ≤ 134217712)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (ceiling inputLimit : Nat)
    (secondNoWrap : secondPointer.toNat + secondLength.toNat < 2^64)
    (secondBound : secondLength.toNat ≤ inputLimit) (limitBound : inputLimit + 9 < 2^64)
    (ordered : frame ≤ scratch) (framePositive : 0 < frame.toNat) (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : (length.toNat / 4 + 7) +
      (secondLength.toNat*((2*secondLength.toNat+1)*15+19)+92637) ≤ s.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s decodeStepCompactCall =
      (some (.returned (.rStruct [.val (.word (0 : BitVec 64)),value])),post)) :
    post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) := by
  have reached := decode_step_compact_table_reaches s kind pointer length consumed array secondPointer secondLength
    heap scratch frame atItem atArray second atHeap heapBound aligned tableBefore inputBound scratchGlobal frameGlobal code (by omega)
  obtain ⟨ready,facts,spent,_,agreement,returned⟩ := reaches_returned_continuation s decodeStepCompactCall
    decodeStepCompactContinuation _ _ _ reached (by rw [run])
  obtain ⟨nibs,count,leaf,atPath,arrayNext,secondNext,scratchNext,frameNext,codeNext,domain⟩ := facts
  cases tailRun : evaluateHOLFiniteState ready decodeStepCompactContinuation with
  | mk result output =>
    rw [tailRun] at returned
    dsimp only at returned
    subst result
    have kept := decode_step_path_completed_workspace ready output array secondPointer secondLength scratch frame nibs count leaf
      ceiling inputLimit arrayNext secondNext secondNoWrap secondBound limitBound scratchNext frameNext codeNext ordered
      framePositive scratchBelow (by intro address lower upper; rw [domain]; exact arena address lower upper)
      (remainingBudget budget spent) atPath value tailRun
    have globals := agreement.2.2.2.1
    rw [run,tailRun] at globals
    change post.globals = output.globals at globals
    rw [globals]
    exact kept

#print axioms decode_step_compact_call_completed_workspace
end InitECandidate.Runtime
