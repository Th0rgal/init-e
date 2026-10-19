import InitECandidate.Runtime.WitnessDecodeAllocationStack
import InitECandidate.Runtime.WitnessDecodeCompletedNodeEnvelope
import InitECandidate.Runtime.WitnessResultAboveStack
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem witness_decode_mode_result_above_stack {F : Type} (s post : PanSemStateFiniteExact 64 F)
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
    post.locals.lookup (ofString "mode")=some (.val (.word (2#64))) ∨
      ∃ node : BitVec 64, post.locals.lookup (ofString "mode")=some (.val (.word (0#64))) ∧
        post.locals.lookup (ofString "result")=some (.val (.word node)) ∧
        WitnessResultAboveStack post input inputLength previous node persistentFloor ceiling := by
  obtain ⟨nextHeap,heapPost,growth,capped,finishAligned,memory⟩ := witness_decode_mode_normal_heap_frame
    s post table pointer length scratch frame array previous ceiling inputLimit atTop atTable atPointer atLength
    inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    budget heap arrayBound aligned countLimit heapArena inputBeforeFrame inputBeforeArray arrayAbove limitCap run
  have metadata := evaluateHOLFiniteState_metadata s decodeWitnessNodeDecodeMode
  rw [run] at metadata
  have oldStack := stack.after_frame s post input inputLength array previous persistentFloor ceiling
    metadata.2.1 array ceiling (Nat.le_refl _) (Nat.le_refl _) memory
  have result := witness_decode_mode_completed_node_envelope s post table pointer length scratch frame array ceiling inputLimit
    atTable atPointer atLength inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    budget heap arrayBound aligned countLimit heapArena inputBeforeFrame inputBeforeArray arrayAbove limitCap run
  rcases result with pending | ⟨node,mode,localNode,envelope⟩
  · exact Or.inl pending
  · exact Or.inr ⟨node,mode,localNode,witness_result_above_stack_of_completed post input inputLength array previous node
      persistentFloor ceiling oldStack envelope⟩

#print axioms witness_decode_mode_result_above_stack
end InitECandidate.Runtime
