import InitECandidate.Runtime.DecodeHeaderSlicesMemoryReach
import InitECandidate.Runtime.DecodeHeaderSliceLocalsReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

/-- Actual slice construction and both projection declarations reach the
header count check with a readable table and the real array/count locals. -/
theorem decode_header_slice_setup_memory_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer size consumed scratch frame array input inputLength : BitVec 64) (ceiling inputLimit : Nat)
    (atTop : s.locals.lookup (ofString "top") =
      some (.rStruct [.val (.word (1#64)),.val (.word pointer),.val (.word size),.val (.word consumed)]))
    (noWrap : pointer.toNat + size.toNat < 2^64) (lengthBound : size.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (inputBeforeFrame : pointer.toNat + size.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + size.toNat ≤ array.toNat)
    (starts : input.toNat ≤ pointer.toNat) (ends : pointer.toNat + size.toNat ≤ input.toNat + inputLength.toNat)
    (budget : decodeHeaderSlicesCost inputLimit ≤ s.clock) :
    Reaches s (decodeHeaderAt 2)
      (fun ready => ∃ count : BitVec 64,
        count.toNat ≤ inputLength.toNat ∧
        ready.locals = ((s.locals.update (ofString "lst",.rStruct [.val (.word array),.val (.word count)])).update
          (ofString "arr",.val (.word array))).update (ofString "n",.val (.word count)) ∧
        RlpSliceInputPrefix ready array input inputLength count.toNat ∧
        ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd array (count * 16)))) ∧
        ready.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
        ready.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
        ready.memaddrs = s.memaddrs ∧ ready.code = s.code ∧
        array.toNat + count.toNat * 16 ≤ (allocationEnd array (count * 16)).toNat ∧
        (allocationEnd array (count * 16)).toNat ≤ 33806089496 ∧ (allocationEnd array (count * 16)).toNat % 8 = 0 ∧
        (∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < array.toNat → ready.memory address = s.memory address))
      (decodeHeaderSlicesCost inputLimit) (decodeHeaderAt 5) := by
  have slices := decode_header_slices_memory_reaches s pointer size consumed scratch frame array input inputLength ceiling inputLimit
    atTop noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap arrayBound
    countLimit heapArena inputBeforeFrame inputBeforeArray starts ends budget
  apply reaches_trans s (decodeHeaderAt 2) (decodeHeaderAt 3) (decodeHeaderAt 5) _ _
    (decodeHeaderSlicesCost inputLimit) 0 slices
  intro ready facts
  obtain ⟨count,countBound,locals,table,heapBinding,scratchBinding,frameBinding,domain,installed,extent,cap,al,memory⟩ := facts
  have atList : ready.locals.lookup (ofString "lst") = some (.rStruct [.val (.word array),.val (.word count)]) := by
    rw [locals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE]
  apply reaches_mono ready (decodeHeaderAt 3) (decodeHeaderAt 5) _ _ 0 0 (le_refl _) ?_
    (decode_header_slice_locals_reaches ready array count atList)
  intro post same
  subst post
  refine ⟨count,countBound,?_,?_,heapBinding,scratchBinding,frameBinding,domain,installed,extent,cap,al,memory⟩
  · change ((ready.locals.update _).update _) = _
    rw [locals]
  · exact table.after_memory_below ready _ array count input inputLength (allocationEnd array (count * 16)) extent rfl (fun _ _ => rfl)

#print axioms decode_header_slice_setup_memory_reaches
end InitECandidate.Runtime
