import InitECandidate.Runtime.DecodeStepCompactReach
import InitECandidate.Runtime.CompactNibbleHeapWordFrame
import InitECandidate.Runtime.ThreeWordValueShape
import InitECandidate.Runtime.TxFixedBytesArguments
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual compact decoding keeps the readable second slice below its initial
heap frontier. The real returned callee run establishes the memory frame. -/
theorem decode_step_compact_table_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
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
    (code : s.code = originalRuntimeCode) (budget : length.toNat / 4 + 7 ≤ s.clock) :
    Reaches s decodeStepCompactCall
      (fun next => ∃ nibs count leaf : BitVec 64,
        next.locals.lookup (ofString "cn") = some
          (.rStruct [.val (.word nibs),.val (.word count),.val (.word leaf)]) ∧
        next.locals.lookup (ofString "arr") = some (.val (.word array)) ∧
        RlpSliceEntry next array 1 secondPointer secondLength ∧
        next.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
        next.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
        next.code = originalRuntimeCode ∧ next.memaddrs = s.memaddrs)
      (length.toNat / 4 + 7) decodeStepCompactContinuation := by
  have reached := decode_step_compact_reaches s kind pointer length consumed (by omega) atItem code budget
  rcases reached with ⟨next,facts,spent,remaining,agreement⟩ | aborted
  · obtain ⟨value,post,bodyRun,shape,nextEq,nextCode,domain,scratchKept,frameKept⟩ := facts
    obtain ⟨nibs,count,leaf,rfl⟩ := value_three_words_of_checked_shape value shape
    let entry := callEntryStateHOLFinite s (compactNibbleCallee pointer length)
    have p : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
      simp (config := {decide := true}) [entry,compactNibbleCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have n : entry.locals.lookup (ofString "n") = some (.val (.word length)) := by
      simp [entry,compactNibbleCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have frameMemory := compact_nibble_body_returned_memory_below_heap entry post pointer length heap p n code atHeap
      heapBound inputBound aligned _ bodyRun
    have pointerNat : (array + 16#64).toNat = array.toNat + 16 := by
      rw [BitVec.toNat_add_of_lt (by change array.toNat + 16 < 2^64; omega)]
      rfl
    have lengthNat : (array + 24#64).toNat = array.toNat + 24 := by
      rw [BitVec.toNat_add_of_lt (by change array.toNat + 24 < 2^64; omega)]
      rfl
    have pointerMemory : next.memory (array + 1 * 16#64) = s.memory (array + 1 * 16#64) := by
      rw [nextEq]
      change post.memory (array + 1 * 16#64) = s.memory (array + 1 * 16#64)
      apply frameMemory
      rw [show (1 : BitVec 64) * 16#64 = 16#64 from by decide,pointerNat]
      omega
    have lengthMemory : next.memory (array + 1 * 16#64 + 8#64) = s.memory (array + 1 * 16#64 + 8#64) := by
      rw [nextEq]
      change post.memory (array + 1 * 16#64 + 8#64) = s.memory (array + 1 * 16#64 + 8#64)
      apply frameMemory
      rw [show (1 : BitVec 64) * 16#64 = 16#64 from by decide,BitVec.add_assoc,
        show (16#64 + 8#64) = 24#64 from by decide,lengthNat]
      omega
    have secondKept := RlpSliceEntry.after_frame s next array 1 secondPointer secondLength second domain pointerMemory lengthMemory
    refine Or.inl ⟨next,⟨nibs,count,leaf,?_,?_,secondKept,scratchKept.trans scratchGlobal,
      frameKept.trans frameGlobal,nextCode.trans code,domain⟩,spent,remaining,agreement⟩
    · rw [nextEq]
      simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · rw [nextEq]
      simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
        show ofString "cn" ≠ ofString "arr" by decide] using atArray
  · exact Or.inr aborted

#print axioms decode_step_compact_table_reaches
end InitECandidate.Runtime
