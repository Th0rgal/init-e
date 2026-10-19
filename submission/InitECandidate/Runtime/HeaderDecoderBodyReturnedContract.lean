import InitECandidate.Runtime.HeaderDecoderBodyBound
import InitECandidate.Runtime.DecodeHeaderInitialFieldsMemoryReach
import InitECandidate.Runtime.HeaderDecoderFieldsReturnedFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 200000

/-- A successful original header decoder returns its actual allocated record,
restores the parser workspace, advances a bounded heap and keeps older heap words. -/
theorem header_decoder_body_returned_contract {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame array : BitVec 64) (ceiling inputLimit : Nat)
    (atPointer : s.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : s.locals.lookup (ofString "len") = some (.val (.word length)))
    (noWrap : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → s.memaddrs address)
    (heap : s.globals.lookup (ofString "heap_ptr") = some (.val (.word array)))
    (arrayBound : array.toNat ≤ 33806089496) (countLimit : inputLimit * 16 < 2^64)
    (heapArena : ∀ address : BitVec 64, array.toNat ≤ address.toNat → address.toNat < 33806089496 → s.memaddrs address)
    (ceilingAligned : ceiling % 8 = 0) (inputAfter : ceiling ≤ pointer.toNat)
    (inputBeforeArray : pointer.toNat + length.toNat ≤ array.toNat)
    (budget : headerDecoderBodyCost inputLimit ≤ s.clock) (value : ValueHOL 64)
    (run : evaluateHOLFiniteState s (sourceFunctionBody Guest.guestFn_decode_header) = (some (.returned value),post)) :
    ∃ count : BitVec 64,
      count.toNat ≤ length.toNat ∧ count.toNat ≤ 23 ∧ value = .val (.word (allocationEnd array (count * 16))) ∧
      array.toNat + count.toNat * 16 ≤ (allocationEnd array (count * 16)).toNat ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd (allocationEnd array (count * 16)) 248))) ∧
      post.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)) ∧
      post.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)) ∧
      post.memaddrs = s.memaddrs ∧ post.code = s.code ∧
      (allocationEnd array (count * 16)).toNat + 248 ≤ (allocationEnd (allocationEnd array (count * 16)) 248).toNat ∧
      (allocationEnd (allocationEnd array (count * 16)) 248).toNat ≤ 33806089496 ∧
      (allocationEnd (allocationEnd array (count * 16)) 248).toNat % 8 = 0 ∧
      (∀ address : BitVec 64, ceiling ≤ address.toNat → address.toNat < array.toNat → post.memory address = s.memory address) := by
  have boundedPrefix := decode_header_initial_fields_memory_reaches s pointer length scratch frame array ceiling inputLimit atPointer atLength noWrap lengthBound
    limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena heap arrayBound countLimit heapArena
    ceilingAligned inputAfter inputBeforeArray (by unfold headerDecoderBodyCost at budget; omega)
  have sourceRun : evaluateHOLFiniteState s (decodeHeaderAt 0) = (some (.returned value),post) := by
    rw [← source_decode_header_body]
    exact run
  obtain ⟨ready,facts,spent,_,agreement,returnedTail⟩ := reaches_returned_continuation s (decodeHeaderAt 0) (decodeHeaderAt 9) _
    (decodeHeaderRlpCost inputLimit + decodeHeaderSlicesCost inputLimit + 2) value boundedPrefix (by rw [sourceRun])
  obtain ⟨count,flag,countBound,accepted,arr,n,flagLocal,header,table,heapBinding,scratchBinding,frameBinding,
    domain,installed,extent,cap,aligned,oldMemory⟩ := facts
  have countSmall : count.toNat ≤ 23 := by
    rcases accepted with ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> decide
  have sizeNat : (count * 16).toNat = count.toNat * 16 := by
    rw [BitVec.toNat_mul_of_lt (by change count.toNat * 16 < 2^64; omega)]
    rfl
  have before : array.toNat + count.toNat * 16 ≤ (allocationEnd array (count * 16)).toNat := by
    have covers := allocationEnd_covers_noWrap array (count * 16) (by rw [sizeNat]; omega)
    simpa only [sizeNat] using covers
  have g : HeaderDecoderGeometry array count length scratch frame (allocationEnd array (count * 16)) flag ceiling inputLimit :=
    ⟨before,by omega,by omega,by omega,lengthBound,limitBound,orderedFrame,framePositive,scratchBelow,accepted⟩
  have c : HeaderDecoderContext ready array count pointer length scratch frame (allocationEnd array (count * 16)) flag ceiling :=
    ⟨arr,header,flagLocal,table,scratchBinding,frameBinding,installed.trans code,by
      intro address lo hi
      rw [domain]
      exact arena address lo hi⟩
  let tailPost := (evaluateHOLFiniteState ready (decodeHeaderAt 9)).2
  have tailRun : evaluateHOLFiniteState ready (decodeHeaderAt 9) = (some (.returned value),tailPost) := Prod.ext returnedTail rfl
  obtain ⟨valueEq,_,_,globals,memory⟩ := header_fields_returned_frame ready tailPost array count pointer length scratch frame
    (allocationEnd array (count * 16)) flag ceiling inputLimit g c (by unfold headerDecoderBodyCost at budget; omega) value tailRun
  have sourceMemory := agreement.2.2.1
  have sourceGlobals := agreement.2.2.2.1
  rw [sourceRun] at sourceMemory sourceGlobals
  have metadata := evaluateHOLFiniteState_metadata s (sourceFunctionBody Guest.guestFn_decode_header)
  rw [run] at metadata
  refine ⟨count,countBound,countSmall,valueEq,before,?_,?_,?_,metadata.2.1,metadata.1,extent,cap,aligned,?_⟩
  · rw [sourceGlobals]
    exact (globals (ofString "heap_ptr")).trans heapBinding
  · rw [sourceGlobals]
    exact (globals (ofString "scratch_ptr")).trans scratchBinding
  · rw [sourceGlobals]
    exact (globals (ofString "frame_mem_ptr")).trans frameBinding
  · intro address lo hi
    rw [sourceMemory]
    exact (memory address lo (by omega)).trans (oldMemory address lo hi)

#print axioms header_decoder_body_returned_contract
end InitECandidate.Runtime
