import InitECandidate.Runtime.PayloadSplitHeaderFrame
import InitECandidate.Runtime.PayloadSplitEntryReturned
import InitECandidate.Runtime.PayloadTransactionSpan
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual extra-data header survives transaction decoding and every remaining payload store. -/
theorem payload_offset_returned_extra {F : Type} (state post : PanSemStateFiniteExact 64 F)
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
    ∃ txs : BitVec 64, (txs - 540).toNat ≤ 32 ∧
      RlpSliceEntry post payload 1 (pointer + 540) (txs - 540) := by
  obtain ⟨txs,withdrawals,balance,entry,output,txLower,txUpper,txWd,wdBal,balLength,tail,
      locals,installed,domain,globals,read16,read24,postMemory,postGlobals,postDomain⟩ :=
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
  have frame (offset : BitVec 64) (member : offset = 16 ∨ offset = 24) :
      output.memory (payload + offset) = entry.memory (payload + offset) := by
    apply (payload_split_header_frame entry output payload pointer txs withdrawals balance heapPointer (payload + offset) value
      pl p tx wd bal (by rw [globals]; exact heap) heapBound (by rw [domain]; exact header32)
      (by rw [domain]; exact header40) ?_ ?_ (installed.trans code) tail).1
    · intro later hl
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
      rcases member with rfl | rfl
      all_goals rcases hl with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp
    · have offsetBound : offset.toNat ≤ 24 := by rcases member with rfl | rfl <;> decide
      have natural : (payload + offset).toNat = payload.toNat + offset.toNat := BitVec.toNat_add_of_lt (by omega)
      rw [natural]; omega
  have metadata := evaluateHOLFiniteState_metadata state (payloadAt 4)
  rw [run] at metadata
  have small : (txs - (540 : BitVec 64)).toNat ≤ 32 := by
    rw [BitVec.toNat_sub_of_le (show (540 : BitVec 64) ≤ txs from txLower)]
    change txs.toNat - 540 ≤ 32
    omega
  refine ⟨txs,small,?_,?_,?_,?_⟩
  · rw [metadata.2.1]; exact header16
  · simpa [BitVec.add_assoc] using (metadata.2.1 ▸ header24)
  · change post.memory (payload + 16) = _
    rw [postMemory,frame 16 (Or.inl rfl)]
    exact read16
  · change post.memory (payload + 16 + 8) = _
    rw [show payload + 16 + 8 = payload + 24 by simp [BitVec.add_assoc],postMemory,frame 24 (Or.inr rfl)]
    exact read24

#print axioms payload_offset_returned_extra
end InitECandidate.Runtime
