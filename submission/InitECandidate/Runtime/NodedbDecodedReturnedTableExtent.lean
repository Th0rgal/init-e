import InitECandidate.Runtime.NodedbWholeBodyReturnedTableExtent
import InitECandidate.Runtime.NodedbEmptyWholeBodyReturnedTableExtent
import InitECandidate.Runtime.NodedbDecodedReturnedFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
theorem nodedb_decoded_returned_table_extent {F : Type} (s post : PanSemStateFiniteExact 64 F)
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
    ∃ keys stride capacity used values order orderPos count : BitVec 64, ∃ bits : Nat, ∃ finalHeap : BitVec 64,
      count.toNat ≤ total.toNat ∧ capacity.toNat ≤ 536870912 ∧ count.toNat < capacity.toNat ∧
      HtabAligned 32 pointer keys stride capacity used values order orderPos count bits post ∧
      OrderInv post capacity count used order orderPos ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
      orderPos.toNat + capacity.toNat * 8 ≤ finalHeap.toNat := by
  by_cases empty : total = 0
  · exact nodedb_empty_whole_body_returned_table_extent s post value total pointer array statePad pad output code
      atTotal empty atArray atState atPad atOutput atHeap aligned capped arena budget run
  · have small : total.toNat ≤ 134217712 := by omega
    obtain ⟨stateEnd,padEnd,outputEnd⟩ := windows empty
    apply nodedb_whole_body_returned_table_extent s post value pointer total array statePad pad output code atHeap
      aligned capped atTotal atArray atState atPad atOutput small outputAligned arrayEnd stateEnd padEnd outputEnd
      arena _ budget run
    intro j inside
    obtain ⟨src,len,valid⟩ := decoded j inside
    exact ⟨src,len,valid.readable.pointerDomain,valid.readable.lengthDomain,valid.readable.pointerCell,
      valid.readable.lengthCell,(valid.length_bound s array j src len input inputLength).trans inputSmall⟩

#print axioms nodedb_decoded_returned_table_extent
end InitECandidate.Runtime
