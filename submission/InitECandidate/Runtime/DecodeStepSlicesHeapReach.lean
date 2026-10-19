import InitECandidate.Runtime.DecodeStepSlicesRuntimeReach
import InitECandidate.Runtime.RlpSlicesBodyMemoryBetween
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Contents and allocator contracts hold in the actual node continuation state. -/
theorem decode_step_slices_heap_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (pointer length consumed scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (atItem : s.locals.lookup (ofString "it") = some
      (.rStruct [.val (.word (1#64)),.val (.word pointer),.val (.word length),.val (.word consumed)]))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (budget : decodeStepSlicesCost length.toNat ≤ s.clock)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (inputBeforeFrame : pointer.toNat + length.toNat ≤ frame.toNat ∨ (ceiling % 8 = 0 ∧ ceiling ≤ pointer.toNat))
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat) :
    Reaches s (decodeStepAt 4)
      (fun next => ∃ count : BitVec 64,
        next.locals.lookup (ofString "sl") = some (.rStruct [.val (.word array),.val (.word count)]) ∧
        count.toNat ≤ length.toNat ∧ RlpSliceInputPrefix next array pointer length count.toNat ∧
        next.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd array (count * 16)))) ∧
        next.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
        next.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
        array.toNat + count.toNat * 16 ≤ 33806089496 ∧
        (allocationEnd array (count * 16)).toNat ≤ 33806089496 ∧
        (allocationEnd array (count * 16)).toNat % 8 = 0 ∧
        next.code = s.code ∧ next.memaddrs = s.memaddrs ∧
        next.locals = s.locals.update (ofString "sl",.rStruct [.val (.word array),.val (.word count)]) ∧
        (∀ watched : BitVec 64, ceiling ≤ watched.toNat → watched.toNat < array.toNat →
          next.memory watched = s.memory watched))
      (decodeStepSlicesCost length.toNat) (decodeStepAt 5) := by
  have reached := decode_step_slices_reaches s pointer length consumed scratch frame ceiling inputLimit atItem
    noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
  apply reaches_mono s (decodeStepAt 4) (decodeStepAt 5) _ _ _ _ (Nat.le_refl _) _ reached
  intro next witness
  obtain ⟨value,post,run,_,rfl⟩ := witness
  let entry := callEntryStateHOLFinite s (rlpHeaderCallee pointer length)
  have p : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp (config := {decide := true}) [entry,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have n : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨count,rfl,bound,slicePrefix,heapPost,scratchPost,framePost,interval,endpoint,aligned⟩ :=
    rlpSlices_body_returned_runtime_contract entry post pointer length scratch frame array ceiling inputLimit p n
      noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena
      heap arrayBound countLimit heapArena
      (by change _ ≤ s.clock - 1; unfold decodeStepSlicesCost at budget; omega)
      inputBeforeFrame inputBeforeArray value run
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_list_to_slices)
  rw [run] at metadata
  obtain ⟨_,_,_,_,oldMemory⟩ := rlpSlices_body_returned_memory_between entry post pointer length scratch frame array
    ceiling inputLimit p n noWrap lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive
    scratchBelow arena heap arrayBound countLimit heapArena
    (by change _ ≤ s.clock-1; unfold decodeStepSlicesCost at budget; omega) _ run
  refine ⟨count,?_,bound,?_,heapPost,scratchPost,framePost,interval,endpoint,aligned,metadata.1,metadata.2.1,rfl,?_⟩
  · simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · intro slot inside
    obtain ⟨p,n,entry⟩ := slicePrefix slot inside
    exact ⟨p,n,entry.after_frame _ _ _ _ _ _ _ _ rfl rfl rfl⟩

  · intro watched above before
    exact oldMemory watched before above

#print axioms decode_step_slices_heap_reaches
end InitECandidate.Runtime
