import InitECandidate.Runtime.RlpItemBodyProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A bounded header and input-bounded consumed length place the returned
payload inside the caller's nonwrapping input interval. -/
theorem rlpItem_payload_pointer_range (pointer total header payload : BitVec 64)
    (inputRange : pointer.toNat + total.toNat < 2^64)
    (inputBound : total.toNat + 9 < 2^64)
    (headerBound : header.toNat ≤ 9) (payloadBound : payload.toNat ≤ total.toNat)
    (consumedBound : (header + payload).toNat ≤ total.toNat) :
    (pointer + header).toNat + payload.toNat ≤ pointer.toNat + total.toNat ∧
      (pointer + header).toNat + payload.toNat < 2^64 ∧
      pointer.toNat ≤ (pointer + header).toNat := by
  have consumedNat : (header + payload).toNat = header.toNat + payload.toNat := by
    rw [BitVec.toNat_add_of_lt (by omega)]
  rw [consumedNat] at consumedBound
  have cursorNat : (pointer + header).toNat = pointer.toNat + header.toNat := by
    rw [BitVec.toNat_add_of_lt (by omega)]
  rw [cursorNat]
  omega

#print axioms rlpItem_payload_pointer_range
theorem rlpItem_short_list_full_payload_range {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer total : BitVec 64) (byte : UInt8) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be pointer = some byte)
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (lower : 191 < byte.toNat) (upper : byte.toNat ≤ 247)
    (nonzero : total ≠ 0) (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock)
    (inputRange : pointer.toNat + total.toNat < 2^64) (inputBound : total.toNat + 9 < 2^64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item) = (some (.returned value),post)) :
    (pointer + 1).toNat + ((BitVec.ofNat 64 byte.toNat) - 192).toNat ≤ pointer.toNat + total.toNat ∧
      (pointer + 1).toNat + ((BitVec.ofNat 64 byte.toNat) - 192).toNat < 2^64 ∧
      pointer.toNat ≤ (pointer + 1).toNat := by
  obtain ⟨fields,payloadBound,positive,consumedBound⟩ := rlpItem_short_list_full_return_contract state post pointer total byte value
    pointerLocal loaded totalLocal lower upper nonzero code ticks run
  exact rlpItem_payload_pointer_range pointer total 1 ((BitVec.ofNat 64 byte.toNat) - 192)
    inputRange inputBound (by decide) (by omega) consumedBound

#print axioms rlpItem_short_list_full_payload_range
theorem rlpItem_long_list_full_payload_range {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer total : BitVec 64) (byte : UInt8) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be pointer = some byte)
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (lower : 247 < byte.toNat) (upper : byte.toNat ≤ 255)
    (nonzero : total ≠ 0) (code : state.code = originalRuntimeCode) (ticks : 10 ≤ state.clock)
    (inputRange : pointer.toNat + total.toNat < 2^64) (inputBound : total.toNat + 9 < 2^64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item) = (some (.returned value),post)) :
    ∃ payload : BitVec 64,
      value = .rStruct [.val (.word 1),.val (.word (pointer + (1 + ((BitVec.ofNat 64 byte.toNat) - 247)))),
        .val (.word payload),.val (.word (1 + (((BitVec.ofNat 64 byte.toNat) - 247) + payload)))] ∧
      (pointer + (1 + ((BitVec.ofNat 64 byte.toNat) - 247))).toNat + payload.toNat ≤ pointer.toNat + total.toNat ∧
      (pointer + (1 + ((BitVec.ofNat 64 byte.toNat) - 247))).toNat + payload.toNat < 2^64 ∧
      pointer.toNat ≤ (pointer + (1 + ((BitVec.ofNat 64 byte.toNat) - 247))).toNat := by
  obtain ⟨payload,fields,payloadBound,positive,consumedBound⟩ := rlpItem_long_list_full_return_contract state post pointer total byte value
    pointerLocal loaded totalLocal lower upper nonzero code ticks run
  have headerNat : (BitVec.ofNat 64 byte.toNat).toNat = byte.toNat := by
    change byte.toNat % 2^64 = byte.toNat
    omega
  have small : ((BitVec.ofNat 64 byte.toNat) - 247).toNat ≤ 8 := by
    rw [BitVec.toNat_sub_of_le (by apply BitVec.le_def.mpr; change 247 ≤ (BitVec.ofNat 64 byte.toNat).toNat; omega)]
    change (BitVec.ofNat 64 byte.toNat).toNat - 247 ≤ 8
    omega
  have headerBound : (1 + ((BitVec.ofNat 64 byte.toNat) - 247)).toNat ≤ 9 := by
    rw [BitVec.toNat_add_of_lt (by change 1 + ((BitVec.ofNat 64 byte.toNat) - 247).toNat < 2^64; omega)]
    change 1 + ((BitVec.ofNat 64 byte.toNat) - 247).toNat ≤ 9
    omega
  have range := rlpItem_payload_pointer_range pointer total (1 + ((BitVec.ofNat 64 byte.toNat) - 247)) payload
    inputRange inputBound headerBound (by omega) (by simpa [BitVec.add_assoc] using consumedBound)
  exact ⟨payload,fields,range⟩

#print axioms rlpItem_long_list_full_payload_range
theorem rlpItem_short_string_full_payload_range {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer total : BitVec 64) (byte : UInt8) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be pointer = some byte)
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (lower : 128 ≤ byte.toNat) (upper : byte.toNat ≤ 183)
    (nonzero : total ≠ 0) (code : state.code = originalRuntimeCode) (ticks : 1 ≤ state.clock)
    (inputRange : pointer.toNat + total.toNat < 2^64) (inputBound : total.toNat + 9 < 2^64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item) = (some (.returned value),post)) :
    (pointer + 1).toNat + ((BitVec.ofNat 64 byte.toNat) - 128).toNat ≤ pointer.toNat + total.toNat ∧
      (pointer + 1).toNat + ((BitVec.ofNat 64 byte.toNat) - 128).toNat < 2^64 ∧
      pointer.toNat ≤ (pointer + 1).toNat := by
  obtain ⟨payloadBound,positive,consumedBound⟩ := rlpItem_short_full_return_progress state post pointer total byte value
    pointerLocal totalLocal nonzero lower upper loaded code ticks run
  exact rlpItem_payload_pointer_range pointer total 1 ((BitVec.ofNat 64 byte.toNat) - 128)
    inputRange inputBound (by decide) (by omega) consumedBound

#print axioms rlpItem_short_string_full_payload_range
theorem rlpItem_long_string_full_payload_range {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer total : BitVec 64) (byte : UInt8) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be pointer = some byte)
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (lower : 183 < byte.toNat) (upper : byte.toNat ≤ 191)
    (nonzero : total ≠ 0) (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock)
    (inputRange : pointer.toNat + total.toNat < 2^64) (inputBound : total.toNat + 9 < 2^64)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item) = (some (.returned value),post)) :
    ∃ payload : BitVec 64,
      value = .rStruct [.val ( .word 0),.val (.word (pointer + (1 + ((BitVec.ofNat 64 byte.toNat) - 183)))),
        .val (.word payload),.val (.word (1 + (((BitVec.ofNat 64 byte.toNat) - 183) + payload)))] ∧
      (pointer + (1 + ((BitVec.ofNat 64 byte.toNat) - 183))).toNat + payload.toNat ≤ pointer.toNat + total.toNat ∧
      (pointer + (1 + ((BitVec.ofNat 64 byte.toNat) - 183))).toNat + payload.toNat < 2^64 ∧
      pointer.toNat ≤ (pointer + (1 + ((BitVec.ofNat 64 byte.toNat) - 183))).toNat := by
  obtain ⟨payload,fields,payloadBound,positive,consumedBound⟩ := rlpItem_long_full_return_contract state post pointer total byte value
    pointerLocal totalLocal nonzero lower upper loaded code ticks run
  have headerNat : (BitVec.ofNat 64 byte.toNat).toNat = byte.toNat := by
    change byte.toNat % 2^64 = byte.toNat
    omega
  have small : ((BitVec.ofNat 64 byte.toNat) - 183).toNat ≤ 8 := by
    rw [BitVec.toNat_sub_of_le (by apply BitVec.le_def.mpr; change 183 ≤ (BitVec.ofNat 64 byte.toNat).toNat; omega)]
    change (BitVec.ofNat 64 byte.toNat).toNat - 183 ≤ 8
    omega
  have headerBound : (1 + ((BitVec.ofNat 64 byte.toNat) - 183)).toNat ≤ 9 := by
    rw [BitVec.toNat_add_of_lt (by change 1 + ((BitVec.ofNat 64 byte.toNat) - 183).toNat < 2^64; omega)]
    change 1 + ((BitVec.ofNat 64 byte.toNat) - 183).toNat ≤ 9
    omega
  have range := rlpItem_payload_pointer_range pointer total (1 + ((BitVec.ofNat 64 byte.toNat) - 183)) payload
    inputRange inputBound headerBound (by omega) (by simpa [BitVec.add_assoc] using consumedBound)
  exact ⟨payload,fields,range⟩

#print axioms rlpItem_long_string_full_payload_range
end InitECandidate.Runtime
