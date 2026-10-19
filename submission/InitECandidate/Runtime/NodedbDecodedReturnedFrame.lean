import InitECandidate.Runtime.NodedbEmptyWholeBodyReturnedFrame
import InitECandidate.Runtime.NodedbWholeBodyReturnedFrame
import InitECandidate.Runtime.NodedbDecodedCallBound
/-!
The actual returned frame of the original builder for every decoded entry count.

This is the unified version of `nodedb_whole_body_returned_frame`: the premises
are exactly the body-entry data that `runBounded_nodedb_decoded_call` obtains from
the decoded call (typed `n`/`slice_arr`, the typed heap pointer and the three
workspace globals, `RlpSliceInputPrefix` with `countBound`/`inputSmall`, the
aligned heap and arena, output alignment, the array end, the conditional
workspace windows only in the non-empty case, the body cost budget and the actual
returned body run).

* When `total = 0` the frame is derived by
  `nodedb_empty_whole_body_returned_frame`, which needs no window, no array end,
  no slice premise and no output alignment.
* When `total ≠ 0` the decoded prefix supplies the input slices and the
  conditional windows supply the three window ends, and the frame is
  `nodedb_whole_body_returned_frame`.

No callee frame is assumed in either branch.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- An actual returned run of the original builder, for any decoded entry count,
supplies the entry heap pointer as value, the caller's domain, code and workspace
globals, a real typed monotone aligned bounded live heap and the caller memory
frame below the entry heap pointer outside the workspace windows. -/
theorem nodedb_decoded_returned_frame {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (value : ValueHOL 64) (pointer total array statePad pad output input inputLength : BitVec 64)
    (code : s.code = originalRuntimeCode)
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (aligned : pointer.toNat % 8 = 0) (capped : pointer.toNat ≤ 33806089496)
    (atState : s.globals.lookup (ofString "keccak_st") = some (.val (.word statePad)))
    (atPad : s.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (atOutput : s.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)))
    (atTotal : s.locals.lookup (ofString "n") = some (.val (.word total)))
    (atArray : s.locals.lookup (ofString "slice_arr") = some (.val (.word array)))
    (decoded : RlpSliceInputPrefix s array input inputLength total.toNat)
    (countBound : total.toNat ≤ inputLength.toNat / 4) (inputSmall : inputLength.toNat ≤ 134217712)
    (outputAligned : output.toNat % 8 = 0)
    (arrayEnd : array.toNat + total.toNat * 16 ≤ pointer.toNat)
    (windows : total ≠ 0 → statePad.toNat + 200 ≤ array.toNat ∧ pad.toNat + 136 ≤ array.toNat ∧
      output.toNat + 32 ≤ array.toNat)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → pointer.toNat ≤ a.toNat → a.toNat < 33806089496 →
      s.memaddrs a)
    (budget : nodedbBodyCost total ≤ s.clock)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_nodedb_build) =
      (some (.returned value),post)) :
    value = .val (.word pointer) ∧
    post.memaddrs = s.memaddrs ∧ post.code = s.code ∧
    post.globals.lookup (ofString "keccak_st") = some (.val (.word statePad)) ∧
    post.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)) ∧
    post.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)) ∧
    (∃ finalHeap : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
      pointer.toNat ≤ finalHeap.toNat ∧ finalHeap.toNat % 8 = 0 ∧ finalHeap.toNat ≤ 33806089496 ∧
      (∀ a : BitVec 64, a.toNat % 8 = 0 → finalHeap.toNat ≤ a.toNat → a.toNat < 33806089496 →
        post.memaddrs a)) ∧
    (∀ w : BitVec 64, w.toNat < pointer.toNat → ¬ MWin statePad 200 w →
      ¬ MWin pad 136 w → ¬ MWin output 32 w → post.memory w = s.memory w) := by
  by_cases empty : total = 0
  · obtain ⟨valueEq,codeEq,domainEq,stateGlobal,padGlobal,outputGlobal,heap,heapGlobal,heapAligned,
      headerBelow,heapInside,wordFrame,arenaFrame⟩ :=
      nodedb_empty_whole_body_returned_frame s post value total pointer array statePad pad output code
        atTotal empty atArray atState atPad atOutput atHeap aligned capped arena budget run
    refine ⟨valueEq,domainEq,codeEq,stateGlobal,padGlobal,outputGlobal,
      ⟨heap,heapGlobal,?_,heapAligned,heapInside,?_⟩,?_⟩
    · omega
    · intro a al lo hi
      rw [domainEq]
      exact arena a al (by omega) hi
    · intro w below outsideState outsidePad outsideOutput
      exact wordFrame w below
  · have small : total.toNat ≤ 134217712 := by omega
    obtain ⟨stateEnd,padEnd,outputEnd⟩ := windows empty
    refine nodedb_whole_body_returned_frame s post value pointer total array statePad pad output code atHeap
      aligned capped atTotal atArray atState atPad atOutput small outputAligned arrayEnd stateEnd padEnd
      outputEnd arena ?_ budget run
    intro j inside
    obtain ⟨src,len,valid⟩ := decoded j inside
    exact ⟨src,len,valid.readable.pointerDomain,valid.readable.lengthDomain,valid.readable.pointerCell,
      valid.readable.lengthCell,(valid.length_bound s array j src len input inputLength).trans inputSmall⟩

#print axioms nodedb_decoded_returned_frame
end InitECandidate.Runtime
