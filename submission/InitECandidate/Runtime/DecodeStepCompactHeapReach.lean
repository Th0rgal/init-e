import InitECandidate.Runtime.CompactNibbleReturnedHeap
import InitECandidate.Runtime.DecodeStepCompactTableReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem decode_step_compact_heap_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (kind pointer length consumed heap scratch frame : BitVec 64)
    (atItem : s.locals.lookup (ofString "pi") = some
      (.rStruct [.val (.word kind),.val (.word pointer),.val (.word length),.val (.word consumed)]))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (heapBound : heap.toNat ≤ 33806089496) (aligned : heap.toNat%8=0)
    (inputBound : length.toNat ≤ 134217712)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (budget : length.toNat/4+7 ≤ s.clock) :
    Reaches s decodeStepCompactCall
      (fun next => ∃ nibs count leaf : BitVec 64,
        next.locals = s.locals.update (ofString "cn",
          .rStruct [.val (.word nibs),.val (.word count),.val (.word leaf)]) ∧
        next.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd heap (2*length)))) ∧
        heap.toNat ≤ (allocationEnd heap (2*length)).toNat ∧
        (allocationEnd heap (2*length)).toNat ≤ 33806089496 ∧
        (allocationEnd heap (2*length)).toNat%8=0 ∧
        next.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
        next.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
        next.code = originalRuntimeCode ∧ next.memaddrs = s.memaddrs ∧
        (∀ watched : BitVec 64, watched.toNat < heap.toNat → next.memory watched = s.memory watched))
      (length.toNat/4+7) decodeStepCompactContinuation := by
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
    obtain ⟨heapPost,growth,capped,finishAligned⟩ := compact_nibble_body_returned_heap_contract
      entry post length heap n atHeap heapBound code _ bodyRun
    refine Or.inl ⟨next,⟨nibs,count,leaf,?_,?_,growth,capped,finishAligned,scratchKept.trans scratchGlobal,
      frameKept.trans frameGlobal,nextCode.trans code,domain,?_⟩,spent,remaining,agreement⟩
    · rw [nextEq]
      rfl
    · rw [nextEq]
      exact heapPost
    · intro watched before
      rw [nextEq]
      exact frameMemory watched before
  · exact Or.inr aborted

#print axioms decode_step_compact_heap_reaches
end InitECandidate.Runtime
