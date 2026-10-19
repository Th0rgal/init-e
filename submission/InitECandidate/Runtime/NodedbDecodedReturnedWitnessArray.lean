import InitECandidate.Runtime.NodedbDecodedReturnedFrame
import InitECandidate.Runtime.NodedbEmptyWholeBodyReturnedFrame
import InitECandidate.Runtime.WitnessArrayLinkedWindow
/-!
The actual returned builder keeps a linked witness array for every decoded entry
count.

`nodedb_returned_witness_array` transports an old stateless-input record's linked
witness array to the builder's new allocation frontier, but it needs the
unconditional workspace windows, the entry-bound and the decoded slices of the
non-empty case even when there are no entries.  The version below takes exactly
the body-entry data of `runBounded_nodedb_decoded_call` (typed `n`/`slice_arr`,
typed heap pointer and workspace globals, `RlpSliceInputPrefix` with
`countBound`/`inputSmall`, aligned heap and arena, output alignment, array end and
the workspace windows only conditional on a non-zero count) plus the actual
returned body run, and derives the real final heap and the linked witness array
from `nodedb_decoded_returned_frame`.  With no entries the old record's window is
preserved by the unguarded empty-builder frame, so no window, no array end and no
slice premise is used; the empty second list is kept as an exception.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- The actual first builder retains another linked witness array in the old
record window, including an empty list, at its new allocation frontier, for any
decoded entry count. -/
theorem nodedb_decoded_returned_witness_array {F : Type} (s post : PanSemStateFiniteExact 64 F)
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
      (some (.returned value),post))
    (ceiling : Nat)
    (stateBelow : statePad.toNat + 200 ≤ ceiling) (padBelow : pad.toNat + 136 ≤ ceiling)
    (outputBelow : output.toNat + 32 ≤ ceiling)
    (si first second witnessArray witnessCount witnessInput witnessLength : BitVec 64)
    (linked : WitnessArrayLinked s si first second witnessArray witnessCount witnessInput witnessLength pointer)
    (firstInside : first.toNat < 88) (secondInside : second.toNat < 88)
    (recordAbove : ceiling ≤ si.toNat) (recordBefore : si.toNat + 88 ≤ pointer.toNat)
    (arrayAbove : witnessCount.toNat = 0 ∨ ceiling ≤ witnessArray.toNat) :
    ∃ finalHeap : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
      pointer.toNat ≤ finalHeap.toNat ∧ finalHeap.toNat % 8 = 0 ∧ finalHeap.toNat ≤ 33806089496 ∧
      WitnessArrayLinked post si first second witnessArray witnessCount witnessInput witnessLength finalHeap ∧
      (∀ a : BitVec 64, a.toNat % 8 = 0 → finalHeap.toNat ≤ a.toNat → a.toNat < 33806089496 →
        post.memaddrs a) := by
  obtain ⟨_,domain,_,_,_,_,⟨finalHeap,finalHeapGlobal,monotone,finalAligned,finalBound,finalArena⟩,frame⟩ :=
    nodedb_decoded_returned_frame s post value pointer total array statePad pad output input inputLength code
      atHeap aligned capped atState atPad atOutput atTotal atArray decoded countBound inputSmall outputAligned
      arrayEnd windows arena budget run
  have window : ∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < pointer.toNat →
      post.memory address = s.memory address := by
    intro address lower upper
    by_cases empty : total = 0
    · obtain ⟨_,_,_,_,_,_,_,_,_,_,_,wordFrame,_⟩ :=
        nodedb_empty_whole_body_returned_frame s post value total pointer array statePad pad output code
          atTotal empty atArray atState atPad atOutput atHeap aligned capped arena budget run
      exact wordFrame address upper
    · exact frame address upper (mwin_below (by omega)) (mwin_below (by omega)) (mwin_below (by omega))
  have addressNat (offset : BitVec 64) (inside : offset.toNat < 88) :
      (si + offset).toNat = si.toNat + offset.toNat := by
    have top := pointer.isLt
    rw [BitVec.toNat_add_of_lt (by omega)]
  refine ⟨finalHeap,finalHeapGlobal,monotone,finalAligned,finalBound,?_,finalArena⟩
  exact linked.after_memory_between_or_empty s post si first second witnessArray witnessCount witnessInput
    witnessLength pointer finalHeap ceiling
    (by rw [addressNat first firstInside]; omega) (by rw [addressNat first firstInside]; omega)
    (by rw [addressNat second secondInside]; omega) (by rw [addressNat second secondInside]; omega)
    arrayAbove monotone domain window

#print axioms nodedb_decoded_returned_witness_array
end InitECandidate.Runtime
