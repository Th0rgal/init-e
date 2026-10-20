import InitECandidate.Runtime.PayloadSplitHeapUpper
import InitECandidate.Runtime.PayloadOffsetReturnedSlices
import InitECandidate.Runtime.PayloadSplitReturnedSlicesAbove
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original offset-reading suffix through payload return produces
readable transaction slices wholly inside the original payload input,
with the final array/count header and a capped aligned heap beyond the array. -/
theorem payload_offset_returned_slices_heap_upper {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (offsets length payload pointer heapPointer : BitVec 64) (value : ValueHOL 64)
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (atPayload : state.locals.lookup (ofString "pl") = some (.val (.word payload)))
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (aligned : heapPointer.toNat % 8 = 0)
    (afterPayload : payload.toNat + 136 ≤ heapPointer.toNat)
    (inputFits : pointer.toNat + length.toNat < 2 ^ 64)
    (domain0 : state.memaddrs (offsets + 0)) (domain8 : state.memaddrs (offsets + 8))
    (domain16 : state.memaddrs (offsets + 16)) (domain24 : state.memaddrs (offsets + 24))
    (header16 : state.memaddrs (payload + 16)) (header24 : state.memaddrs (payload + 24))
    (header32 : state.memaddrs (payload + 32)) (header40 : state.memaddrs (payload + 40))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (payloadAt 4) = (some (.returned value),post)) :
    ∃ array count nextHeap : BitVec 64,
      RlpSliceInputPrefix post array pointer length count.toNat ∧ count.toNat ≤ length.toNat / 4 ∧
      post.memory (payload + 32) = .word array ∧ post.memory (payload + 40) = .word count ∧
      post.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat % 8 = 0 ∧ heapPointer.toNat ≤ nextHeap.toNat ∧
      array.toNat + count.toNat * 16 ≤ nextHeap.toNat ∧ (count = 0 ∨ payload.toNat + 136 ≤ array.toNat) ∧
      nextHeap.toNat≤heapPointer.toNat+4*length.toNat+7 := by
  obtain ⟨txs,withdrawals,balance,entry,output,txLower,txUpper,txWd,wdBal,balLength,tail,
      locals,installed,domain,globals,_,_,postMemory,postGlobals,postDomain⟩ :=
    payload_split_entry_returned state post offsets length payload pointer value atOffsets atLength atPayload atPointer
      domain0 domain8 domain16 domain24 header16 header24 code run
  have pl : entry.locals.lookup (ofString "pl") = some (.val (.word payload)) := by
    rw [locals,payload_offset_locals_other _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)]
    exact atPayload
  have p : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    rw [locals,payload_offset_locals_other _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)]
    exact atPointer
  have tx : entry.locals.lookup (ofString "o_txs") = some (.val (.word txs)) := by
    rw [locals]
    simp [payloadOffsetLocals,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "o_bal" ≠ ofString "o_txs" by decide,show ofString "o_wd" ≠ ofString "o_txs" by decide]
  have wd : entry.locals.lookup (ofString "o_wd") = some (.val (.word withdrawals)) := by
    rw [locals]
    simp [payloadOffsetLocals,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "o_bal" ≠ ofString "o_wd" by decide]
  have bal : entry.locals.lookup (ofString "o_bal") = some (.val (.word balance)) := by
    rw [locals]; simp [payloadOffsetLocals,HolFiniteMapExact.lookup_update,FUPDATE]
  have span := payload_transaction_span pointer length txs withdrawals txWd (by omega) inputFits
  obtain ⟨array,count,nextHeap,slicePrefix,countBound,read32,read40,nextGlobal,nextBound,nextAligned,growth,arrayBefore,above,upper⟩ :=
    payload_split_returned_slices_heap_upper entry output payload pointer txs withdrawals balance heapPointer value pl p tx wd bal
      (by rw [globals]; exact heap) heapBound aligned afterPayload (by have inside := span.2.2.1; omega)
      (by rw [domain]; exact header32) (by rw [domain]; exact header40) (installed.trans code) tail
  have finalPrefix : RlpSliceInputPrefix post array pointer length count.toNat := by
    intro index inside
    obtain ⟨p,n,item⟩ := slicePrefix index inside
    have framed := item.after_frame output post array index p n (pointer + txs) (withdrawals - txs)
      postDomain (congrFun postMemory _) (congrFun postMemory _)
    refine ⟨p,n,framed.readable,?_,?_,framed.noWrap⟩
    · have lower := framed.startsWithin
      have start := span.2.1
      omega
    · have upper := framed.endsWithin
      have bounded := span.2.2.1
      omega
  refine ⟨array,count,nextHeap,finalPrefix,?_,?_,?_,?_,nextBound,nextAligned,growth,arrayBefore,above,?_⟩
  · have lengthBound := span.2.2.2
    omega
  · rw [postMemory]; exact read32
  · rw [postMemory]; exact read40
  · rw [postGlobals]; exact nextGlobal

  · have lengthBound:=span.2.2.2
    omega

#print axioms payload_offset_returned_slices_heap_upper
end InitECandidate.Runtime
