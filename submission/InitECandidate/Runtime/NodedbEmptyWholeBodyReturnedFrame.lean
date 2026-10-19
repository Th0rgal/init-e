import InitECandidate.Runtime.NodedbEmptyConstructorLoopEntry
import InitECandidate.Runtime.NodedbBodyConstructorReturnedFrame
/-!
The actual returned frame of the whole original builder when the entry count is
zero.

Root's `nodedb_body_constructor_returned_frame` exposes the real insertion
suffix of an actual returned body run together with the constructor's
`NodedbTableReady`.  With `n = 0` the suffix helper
`nodedb_empty_constructor_loop_entry` turns that contract into the zero-count loop
config and after-declaration invariant without any window geometry, and
`nodedb_empty_declared_suffix_returned_frame` turns the actual suffix run into the
returned frame.  The composition below is therefore an actual-theorem statement
for `total = 0`: no `arrayEnd`, `stateEnd`, `padEnd`, `outputEnd`, no input slice
premise and no output alignment is used or assumed.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- An actual returned run of the original builder with no entries returns the
entry heap pointer and keeps the caller's domain, code, workspace globals and all
caller memory below the entry heap pointer; the live heap is the real typed,
aligned, bounded frontier above it.  Only the constructor's capacity/table work
happens above the entry pointer, so the empty suffix needs no window. -/
theorem nodedb_empty_whole_body_returned_frame {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (value : ValueHOL 64) (total pointer : BitVec 64)
    (array statePad pad output : BitVec 64)
    (code : s.code = originalRuntimeCode)
    (atTotal : s.locals.lookup (ofString "n") = some (.val (.word total)))
    (empty : total = 0)
    (atArray : s.locals.lookup (ofString "slice_arr") = some (.val (.word array)))
    (atState : s.globals.lookup (ofString "keccak_st") = some (.val (.word statePad)))
    (atPad : s.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (atOutput : s.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)))
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (aligned : pointer.toNat % 8 = 0) (capped : pointer.toNat ≤ 33806089496)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → pointer.toNat ≤ a.toNat → a.toNat < 33806089496 →
      s.memaddrs a)
    (budget : nodedbBodyCost total ≤ s.clock)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_nodedb_build) =
      (some (.returned value),post)) :
    value = .val (.word pointer) ∧
      post.code = s.code ∧ post.memaddrs = s.memaddrs ∧
      post.globals.lookup (ofString "keccak_st") = some (.val (.word statePad)) ∧
      post.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) ∧
      post.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)) ∧
      ∃ heap : BitVec 64,
        post.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)) ∧
        heap.toNat % 8 = 0 ∧ pointer.toNat + 72 ≤ heap.toNat ∧ heap.toNat ≤ 33806089496 ∧
        (∀ w : BitVec 64, w.toNat < pointer.toNat → post.memory w = s.memory w) ∧
        (∀ a : BitVec 64, a.toNat % 8 = 0 → heap.toNat ≤ a.toNat → a.toNat < 33806089496 →
          post.memaddrs a) := by
  have small : total.toNat ≤ 134217712 := by rw [empty]; simp
  obtain ⟨capacity,bits,at2,next,tailPost,margin,capacitySmall,bitsLower,power,memory,globals,installed,
    domain,locals,ready,clock,returned,tailClock,tailMemory,tailGlobals,tailDomain⟩ :=
    nodedb_body_constructor_returned_frame s post value total pointer code atTotal small atHeap aligned capped
      arena budget run
  have atTotal2 : at2.locals.lookup (ofString "n") = some (.val (.word total)) :=
    (locals _ (by decide)).trans atTotal
  have atArray2 : at2.locals.lookup (ofString "slice_arr") = some (.val (.word array)) :=
    (locals _ (by decide)).trans atArray
  have atState2 : at2.globals.lookup (ofString "keccak_st") = some (.val (.word statePad)) := by
    rw [globals]; exact atState
  have atPad2 : at2.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) := by
    rw [globals]; exact atPad
  have atOutput2 : at2.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)) := by
    rw [globals]; exact atOutput
  have arena2 : ∀ a : BitVec 64, a.toNat % 8 = 0 → pointer.toNat ≤ a.toNat →
      a.toNat < 33806089496 → at2.memaddrs a := by
    intro a al lo hi
    rw [domain]
    exact arena a al lo hi
  obtain ⟨c,totalZero,capacityAt,tableAt,pointerAt,padAt,arrayAt,outputAt,heap,entry⟩ :=
    nodedb_empty_constructor_loop_entry at2 next pointer capacity total array statePad pad output bits
      ready atTotal2 atArray2 atState2 atPad2 atOutput2 empty arena2
  obtain ⟨valueEq,loopRun,clockEq,memoryEq,globalsEq,domainEq,codeEq,heapGlobal,heapAligned,heapInside,
    stateGlobal,padGlobal,outputGlobal⟩ :=
    nodedb_empty_declared_suffix_returned_frame next tailPost value c heap totalZero entry returned
  have metadata := evaluateHOLFiniteState_metadata s (sourceFunctionBody Guest.guestFn_nodedb_build)
  rw [run] at metadata
  have readyFrame : ∀ w : BitVec 64, w.toNat < pointer.toNat → next.memory w = at2.memory w :=
    ready.2.2.2.2.2.1
  have header : pointer.toNat + 72 ≤ heap.toNat := by
    rw [← tableAt]
    exact entry.headerBelow
  refine ⟨?_,?_,?_,?_,?_,?_,heap,?_,?_,?_,?_,?_,?_⟩
  · rw [valueEq, tableAt]
  · exact metadata.1
  · exact metadata.2.1
  · rw [← tailGlobals, stateGlobal, pointerAt]
  · rw [← tailGlobals, padGlobal, padAt]
  · rw [← tailGlobals, outputGlobal, outputAt]
  · rw [← tailGlobals, heapGlobal]
  · exact heapAligned
  · exact header
  · exact heapInside
  · intro w below
    rw [← tailMemory, memoryEq, readyFrame w below, memory]
  · intro a al lo hi
    rw [metadata.2.1]
    exact arena a al (by omega) hi

#print axioms nodedb_empty_whole_body_returned_frame
end InitECandidate.Runtime
