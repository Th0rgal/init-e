import InitECandidate.Runtime.RlpItemPayloadRange
import InitECandidate.Runtime.RlpItemShortFullProgress
import InitECandidate.Runtime.RlpItemLongFullContract
import InitECandidate.Runtime.RlpItemShortListFullReturn
import InitECandidate.Runtime.RlpItemLongListFullReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Returned item fields with a payload interval contained in the caller input. -/
def RlpItemRange (value : ValueHOL 64) (pointer total : BitVec 64) : Prop :=
  ∃ kind payloadPointer payload consumed : BitVec 64,
    value = .rStruct [.val (.word kind),.val (.word payloadPointer),.val (.word payload),.val (.word consumed)] ∧
      payloadPointer.toNat + payload.toNat ≤ pointer.toNat + total.toNat ∧
      payloadPointer.toNat + payload.toNat < 2^64 ∧ pointer.toNat ≤ payloadPointer.toNat

/-- All five original header paths satisfy one return contract after a
successful first-byte load. No payload-memory readability premise is needed. -/
theorem rlpItem_loaded_return_range {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer total : BitVec 64) (byte : UInt8) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (nonzero : total ≠ 0)
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be pointer = some byte)
    (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock)
    (inputRange : pointer.toNat + total.toNat < 2^64) (inputBound : total.toNat + 9 < 2^64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item) = (some (.returned value),post)) :
    RlpItemRange value pointer total := by
  by_cases single : byte.toNat < 128
  · obtain ⟨output,actual,_⟩ := evaluate_rlpItem_single_byte_body state pointer total byte
      pointerLocal totalLocal nonzero single loaded
    have equal := (Prod.mk.inj (run.symm.trans actual)).1
    have positive : 1 ≤ total.toNat := by
      by_contra bad
      apply nonzero
      apply BitVec.eq_of_toNat_eq
      simpa using (show total.toNat = 0 by omega)
    refine ⟨0,pointer,1,1,?_,?_,?_,by rfl⟩
    · simpa using equal
    · change pointer.toNat + 1 ≤ pointer.toNat + total.toNat
      omega
    · change pointer.toNat + 1 < 2^64
      omega
  by_cases short : byte.toNat ≤ 183
  · obtain ⟨result,output,actual,_,_,_,_,fields,_⟩ := evaluate_rlpItem_short_full_body state pointer total byte
      pointerLocal totalLocal nonzero (by omega) short loaded code (by omega)
    have same := Prod.mk.inj (actual.symm.trans run)
    have exactFields := fields value same.1
    have range := rlpItem_short_string_full_payload_range state post pointer total byte value
      pointerLocal loaded totalLocal (by omega) short nonzero code (by omega) inputRange inputBound run
    exact ⟨0,pointer+1,(BitVec.ofNat 64 byte.toNat)-128,1+((BitVec.ofNat 64 byte.toNat)-128),exactFields,range⟩
  by_cases longString : byte.toNat ≤ 191
  · obtain ⟨rPayload,rFields,range⟩ := rlpItem_long_string_full_payload_range state post pointer total byte value
      pointerLocal loaded totalLocal (by omega) longString nonzero code ticks inputRange inputBound run
    exact ⟨0,pointer+(1+((BitVec.ofNat 64 byte.toNat)-183)),rPayload,
      1+(((BitVec.ofNat 64 byte.toNat)-183)+rPayload),rFields,range⟩
  by_cases shortList : byte.toNat ≤ 247
  · obtain ⟨fields,small,positive,bounded⟩ := rlpItem_short_list_full_return_contract state post pointer total byte value
      pointerLocal loaded totalLocal (by omega) shortList nonzero code (by omega) run
    have range := rlpItem_short_list_full_payload_range state post pointer total byte value
      pointerLocal loaded totalLocal (by omega) shortList nonzero code (by omega) inputRange inputBound run
    exact ⟨1,pointer+1,(BitVec.ofNat 64 byte.toNat)-192,1+((BitVec.ofNat 64 byte.toNat)-192),fields,range⟩
  · have byteBound := byte.toNat_lt_size
    change byte.toNat < 256 at byteBound
    obtain ⟨rPayload,rFields,range⟩ := rlpItem_long_list_full_payload_range state post pointer total byte value
      pointerLocal loaded totalLocal (by omega) (by omega) nonzero code (by omega) inputRange inputBound run
    exact ⟨1,pointer+(1+((BitVec.ofNat 64 byte.toNat)-247)),rPayload,
      1+(((BitVec.ofNat 64 byte.toNat)-247)+rPayload),rFields,range⟩

#print axioms rlpItem_loaded_return_range
end InitECandidate.Runtime
