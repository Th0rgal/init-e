import InitECandidate.Runtime.WitnessDecodeModeHeapFrame
import InitECandidate.Runtime.WitnessDecodeModePlacedMetadata
import InitECandidate.Runtime.WitnessAllocationStackFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Actual decode mode preserves every older saved record and installs its real
fresh linked record on a push. The input slice table is enlarged only by the
explicit original-input containment facts. -/
theorem witness_decode_mode_normal_allocation_stack {F : Type} (s post : PanSemStateFiniteExact 64 F)
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
    ∃ nextHeap : BitVec 64,
      post.globals.lookup (ofString "heap_ptr")=some (.val (.word nextHeap)) ∧
      array.toNat≤nextHeap.toNat ∧ nextHeap.toNat≤33806089496 ∧ nextHeap.toNat%8=0 ∧
      ((post.locals.lookup (ofString "mode")=some (.val (.word (0#64))) ∧
        post.locals.lookup (ofString "top")=some (.val (.word previous)) ∧
        WitnessAllocationStack post input inputLength nextHeap persistentFloor ceiling previous) ∨
       ∃ record : BitVec 64,
        post.locals.lookup (ofString "mode")=some (.val (.word (2#64))) ∧
        post.locals.lookup (ofString "top")=some (.val (.word record)) ∧
        WitnessAllocationStack post input inputLength nextHeap persistentFloor record.toNat record) := by
  obtain ⟨nextHeap,heapPost,growth,capped,finishAligned,memory⟩ := witness_decode_mode_normal_heap_frame s post table pointer length scratch frame array previous ceiling inputLimit atTop atTable atPointer atLength
    inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    budget heap arrayBound aligned countLimit heapArena inputBeforeFrame inputBeforeArray arrayAbove limitCap run
  have metadata := evaluateHOLFiniteState_metadata s decodeWitnessNodeDecodeMode
  rw [run] at metadata
  have oldStack := stack.after_frame s post input inputLength array previous persistentFloor ceiling
    metadata.2.1 array ceiling (Nat.le_refl _) (Nat.le_refl _) memory
  have modeProgress := witness_decode_mode_normal_placed_metadata s post table pointer length scratch frame array previous ceiling inputLimit atTop atTable atPointer atLength
    inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
    budget heap arrayBound aligned countLimit heapArena inputBeforeFrame inputBeforeArray arrayAbove limitCap run
  refine ⟨nextHeap,heapPost,growth,capped,finishAligned,?_⟩
  rcases modeProgress with ⟨mode,top⟩ | ⟨record,top,mode,identity,afterFrame,beforeScratch,accessible,tableData,link⟩
  · exact Or.inl ⟨mode,top.trans atTop,oldStack.after_frame post post input inputLength array previous persistentFloor ceiling
      rfl nextHeap ceiling growth (Nat.le_refl _) (by intro w lo hi; rfl)⟩
  · have tableGlobal := tableData.enlarge_input post record pointer length pointer length input inputLength
      ceiling array.toNat spanLo spanHi
    have liveRecord := witness_physical_record_of_pushed post record previous pointer length input inputLength nextHeap
      ceiling persistentFloor array.toNat tableGlobal (by omega) (by omega) (by omega) floorBeforeHeap accessible link heapPost
    have geometry := placed_pushed_branch_above post record pointer length input inputLength array ceiling tableGlobal
    exact Or.inr ⟨record,mode,top,oldStack.push post input inputLength array nextHeap record previous persistentFloor
      ceiling record.toNat liveRecord floorBeforeHeap growth (by omega) (Nat.le_refl _) geometry⟩

#print axioms witness_decode_mode_normal_allocation_stack
end InitECandidate.Runtime
