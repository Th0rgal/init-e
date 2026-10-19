import InitECandidate.Runtime.NodedbReturnedMemoryWindow
import InitECandidate.Runtime.WitnessArrayLinkedWindow
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
/-- The actual first builder retains another linked witness array in the old
record window, including an empty list, at its new allocation frontier. -/
theorem nodedb_returned_witness_array {F : Type} (s post : PanSemStateFiniteExact 64 F) (value : ValueHOL 64)
    (pointer total array statePad pad output : BitVec 64)
    (code : s.code = originalRuntimeCode)
    (atHeap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (aligned : pointer.toNat % 8 = 0) (capped : pointer.toNat ≤ 33806089496)
    (atTotal : s.locals.lookup (ofString "n") = some (.val (.word total)))
    (atArray : s.locals.lookup (ofString "slice_arr") = some (.val (.word array)))
    (atState : s.globals.lookup (ofString "keccak_st") = some (.val (.word statePad)))
    (atPad : s.globals.lookup (ofString "keccak_pad") = some (.val (.word pad)))
    (atOutput : s.globals.lookup (ofString "mpt_hash_scratch") = some (.val (.word output)))
    (small : total.toNat ≤ 134217712)
    (outputAligned : output.toNat % 8 = 0)
    (arrayEnd : array.toNat + total.toNat * 16 ≤ pointer.toNat)
    (stateEnd : statePad.toNat + 200 ≤ array.toNat) (padEnd : pad.toNat + 136 ≤ array.toNat)
    (outputEnd : output.toNat + 32 ≤ array.toNat)
    (arena : ∀ a : BitVec 64, a.toNat % 8 = 0 → pointer.toNat ≤ a.toNat → a.toNat < 33806089496 → s.memaddrs a)
    (slices : ∀ j : BitVec 64, j.toNat < total.toNat → ∃ source size : BitVec 64,
      s.memaddrs (array + j * (16#64)) ∧ s.memaddrs (array + j * (16#64) + (8#64)) ∧
      s.memory (array + j * (16#64)) = .word source ∧ s.memory (array + j * (16#64) + (8#64)) = .word size ∧
      size.toNat ≤ 134217712)
    (budget : nodedbBodyCost total ≤ s.clock)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_nodedb_build) = (some (.returned value),post))
    (ceiling : Nat)
    (stateBelow : statePad.toNat + 200 ≤ ceiling) (padBelow : pad.toNat + 136 ≤ ceiling)
    (outputBelow : output.toNat + 32 ≤ ceiling)
    (si first second secondArray secondCount input inputLength : BitVec 64)
    (linked : WitnessArrayLinked s si first second secondArray secondCount input inputLength pointer)
    (firstInside : first.toNat < 88) (secondInside : second.toNat < 88)
    (recordAbove : ceiling ≤ si.toNat) (recordBefore : si.toNat + 88 ≤ pointer.toNat)
    (secondAbove : secondCount.toNat = 0 ∨ ceiling ≤ secondArray.toNat) :
    ∃ finalHeap : BitVec 64, post.globals.lookup (ofString "heap_ptr") = some (.val (.word finalHeap)) ∧
      pointer.toNat ≤ finalHeap.toNat ∧ finalHeap.toNat % 8 = 0 ∧ finalHeap.toNat ≤ 33806089496 ∧
      WitnessArrayLinked post si first second secondArray secondCount input inputLength finalHeap ∧
      (∀ a : BitVec 64, a.toNat % 8 = 0 → finalHeap.toNat ≤ a.toNat → a.toNat < 33806089496 → post.memaddrs a) := by
  obtain ⟨_,domain,_,_,_,_,⟨finalHeap,atHeap,monotone,finalAligned,finalBound,finalArena⟩,frame⟩ :=
    nodedb_whole_body_returned_frame s post value pointer total array statePad pad output code atHeap aligned capped
      atTotal atArray atState atPad atOutput small outputAligned arrayEnd stateEnd padEnd outputEnd arena slices budget run
  have window : ∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < pointer.toNat →
      post.memory address = s.memory address := by
    intro address lower upper
    exact frame address upper (mwin_below (by omega)) (mwin_below (by omega)) (mwin_below (by omega))
  have addressNat (offset : BitVec 64) (inside : offset.toNat < 88) :
      (si + offset).toNat = si.toNat + offset.toNat := by
    have top := pointer.isLt
    rw [BitVec.toNat_add_of_lt (by omega)]
  refine ⟨finalHeap,atHeap,monotone,finalAligned,finalBound,?_,finalArena⟩
  exact linked.after_memory_between_or_empty s post si first second secondArray secondCount input inputLength
    pointer finalHeap ceiling
    (by rw [addressNat first firstInside]; omega) (by rw [addressNat first firstInside]; omega)
    (by rw [addressNat second secondInside]; omega) (by rw [addressNat second secondInside]; omega)
    secondAbove monotone domain window

#print axioms nodedb_returned_witness_array
end InitECandidate.Runtime
