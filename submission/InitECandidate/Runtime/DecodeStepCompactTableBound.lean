import InitECandidate.Runtime.DecodeStepCompactTableReach
import InitECandidate.Runtime.DecodeStepPathDispatchBound
import InitECandidate.Runtime.RunBoundedReaches
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual compact decoding, retained second-slice parse, and both leaf/extension
continuations have an all-outcome bound with no allocation-room premises. -/
theorem runBounded_decode_step_compact_table_call {F : Type} (s : PanSemStateFiniteExact 64 F)
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
      (secondLength.toNat*((2*secondLength.toNat+1)*15+19)+92637) ≤ s.clock) :
    RunBounded s decodeStepCompactCall ((length.toNat / 4 + 7) +
      (secondLength.toNat*((2*secondLength.toNat+1)*15+19)+92637)) := by
  have reached := decode_step_compact_table_reaches s kind pointer length consumed array secondPointer secondLength
    heap scratch frame atItem atArray second atHeap heapBound aligned tableBefore inputBound scratchGlobal frameGlobal code (by omega)
  apply RunBounded.ofReaches budget reached
  intro next facts ticks
  obtain ⟨nibs,count,leaf,atPath,arrayNext,secondNext,scratchNext,frameNext,codeNext,domain⟩ := facts
  exact runBounded_decode_step_compact_continuation next array secondPointer secondLength scratch frame nibs count leaf
    ceiling inputLimit arrayNext secondNext secondNoWrap secondBound limitBound scratchNext frameNext codeNext ordered
    framePositive scratchBelow (by intro address lower upper; rw [domain]; exact arena address lower upper) ticks atPath

#print axioms runBounded_decode_step_compact_table_call
end InitECandidate.Runtime
