import InitECandidate.Runtime.WitnessDecodeAllocationStack
import InitECandidate.Runtime.WitnessDecodeModeProgress
import InitECandidate.Runtime.WitnessStackChildCreditFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual decode mode decreases the physical measure: completion spends its
mode credit; a real scratch-record push strictly spends capacity. -/
theorem witness_decode_mode_measure_decreases {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (table pointer length scratch frame array previous : BitVec 64) (ceiling inputLimit : Nat)
    (atTop : s.locals.lookup (ofString "top") = some (.val (.word previous)))
    (atTable : s.locals.lookup (ofString "db") = some (.val (.word table)))
    (atPointer : s.locals.lookup (ofString "cur_p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "cur_n") = some (.val (.word length)))
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : decodeStepBodyCost inputLimit + 1 ≤ s.clock)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (aligned : array.toNat%8=0) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (arrayAbove : ceiling ≤ array.toNat) (limitCap : inputLimit ≤ 134217712)
    (input inputLength : BitVec 64) (persistentFloor : Nat)
    (floorAbove : ceiling ≤ persistentFloor) (floorBeforeHeap : persistentFloor ≤ array.toNat)
    (spanLo : input.toNat ≤ pointer.toNat)
    (spanHi : pointer.toNat+length.toNat ≤ input.toNat+inputLength.toNat)
    (stack : WitnessAllocationStack s input inputLength array persistentFloor ceiling previous)
    (run : evaluateHOLFiniteState s decodeWitnessNodeDecodeMode = (none,post)) :
    (post.locals.lookup (ofString "mode")=some (.val (.word (0#64))) ∧
      post.locals.lookup (ofString "top")=some (.val (.word previous)) ∧
      decodeWitnessMeasure (decoderScratchCapacity frame post) previous (witnessTraversalChildCredit post previous) 1 <
        decodeWitnessMeasure (decoderScratchCapacity frame s) previous (witnessTraversalChildCredit s previous) 2) ∨
    ∃ record : BitVec 64, post.locals.lookup (ofString "mode")=some (.val (.word (2#64))) ∧
      post.locals.lookup (ofString "top")=some (.val (.word record)) ∧
      decodeWitnessMeasure (decoderScratchCapacity frame post) record (witnessTraversalChildCredit post record) 3 <
        decodeWitnessMeasure (decoderScratchCapacity frame s) previous (witnessTraversalChildCredit s previous) 2 := by
  obtain ⟨nextHeap,heapPost,growth,capped,finishAligned,memory⟩ := witness_decode_mode_normal_heap_frame
    s post table pointer length scratch frame array previous ceiling inputLimit atTop atTable atPointer atLength
    inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    budget heap arrayBound aligned countLimit heapArena inputBeforeFrame inputBeforeArray arrayAbove limitCap run
  have childCredit := witness_stack_child_credit_after_frame s post input inputLength array previous persistentFloor ceiling
    (stack.physical s input inputLength array previous persistentFloor ceiling) floorBeforeHeap
    (by intro watched lo hi notHash; exact memory watched lo hi)
  have progress := witness_decode_mode_normal_progress s post table pointer length scratch frame array ceiling inputLimit
    atTable atPointer atLength inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
    scratchBelow arena budget heap arrayBound countLimit heapArena inputBeforeFrame inputBeforeArray arrayAbove limitCap run
  rcases progress with ⟨capacity,topPost,modePost⟩ | ⟨capacity,record,identity,topPost,modePost,slot,slotKind,slotPost⟩
  · refine Or.inl ⟨modePost,topPost.trans atTop,?_⟩
    rw [capacity,childCredit]
    exact decodeWitnessMeasure_mode (decoderScratchCapacity frame s) previous (witnessTraversalChildCredit s previous) 2 1 (by decide)
  · refine Or.inr ⟨record,modePost,topPost,?_⟩
    exact decodeWitnessMeasure_push (decoderScratchCapacity frame s) (decoderScratchCapacity frame post) previous record
      (witnessTraversalChildCredit s previous) (witnessTraversalChildCredit post record) 2 3 capacity
      (witnessTraversalChildCredit_bound post record) (by decide)

#print axioms witness_decode_mode_measure_decreases
end InitECandidate.Runtime
