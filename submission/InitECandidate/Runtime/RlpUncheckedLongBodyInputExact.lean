import InitECandidate.Runtime.RlpUncheckedLongStringInputExact
import InitECandidate.Runtime.RlpUncheckedLongListInputExact
import InitECandidate.Runtime.RlpUncheckedReturnedAfterLoad
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The unchecked whole-function result inherits the checked header input bound. -/
theorem rlpUnchecked_long_string_body_input_exact {F : Type}
    (checked unchecked checkedPost uncheckedPost : PanSemStateFiniteExact 64 F)
    (pointer total : BitVec 64) (byte : UInt8) (checkedValue uncheckedValue : ValueHOL 64)
    (checkedPointer : checked.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (checkedTotal : checked.locals.lookup (ofString "len") = some (.val (.word total)))
    (uncheckedPointer : unchecked.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lower : 183 < byte.toNat) (upper : byte.toNat ≤ 191) (nonzero : total ≠ 0)
    (checkedCode : checked.code = originalRuntimeCode) (uncheckedCode : unchecked.code = originalRuntimeCode)
    (ticks : 11 ≤ checked.clock) (uncheckedTicks : 10 ≤ unchecked.clock)
    (loaded : @panMemLoadByteHOL 64 _ checked.memory checked.memaddrs
      (fun address => Classical.propDecidable (checked.memaddrs address)) checked.be pointer = some byte)
    (reads : ∀ offset : Nat, offset < total.toNat → @panMemLoadByteHOL 64 _ checked.memory checked.memaddrs
        (fun address => Classical.propDecidable (checked.memaddrs address)) checked.be (pointer + BitVec.ofNat 64 offset) =
      @panMemLoadByteHOL 64 _ unchecked.memory unchecked.memaddrs
        (fun address => Classical.propDecidable (unchecked.memaddrs address)) unchecked.be (pointer + BitVec.ofNat 64 offset))
    (checkedRun : evaluateHOLFiniteState checked (sourceFunctionBody Guest.guestFn_rlp_item_header) = (some (.returned checkedValue),checkedPost))
    (uncheckedRun : evaluateHOLFiniteState unchecked (sourceFunctionBody Guest.guestFn_rlp_item_total_unchecked) = (some (.returned uncheckedValue),uncheckedPost)) :
    ∃ headerSize payloadSize kind : BitVec 64,
      checkedValue = .rStruct [.val (.word headerSize),.val (.word payloadSize),.val (.word kind)] ∧
      uncheckedValue = .val (.word (headerSize + payloadSize)) := by
  have totalPositive : 0 < total.toNat := by
    by_contra bad
    apply nonzero
    apply BitVec.eq_of_toNat_eq
    simpa using (show total.toNat = 0 by omega)
  have pointerRead := reads 0 totalPositive
  simp only [BitVec.add_zero] at pointerRead
  have uncheckedLoaded : @panMemLoadByteHOL 64 _ unchecked.memory unchecked.memaddrs
      (fun address => Classical.propDecidable (unchecked.memaddrs address)) unchecked.be pointer = some byte :=
    pointerRead.symm.trans loaded
  obtain ⟨output,bodyRun⟩ := rlpUnchecked_returned_after_load unchecked uncheckedPost pointer byte uncheckedValue uncheckedPointer uncheckedLoaded uncheckedRun
  let entered := setVarHOLFinite (ofString "b") (.val (.word (BitVec.ofNat 64 byte.toNat))) unchecked
  have atPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "b" ≠ ofString "p" by decide] using uncheckedPointer
  have atByte : entered.locals.lookup (ofString "b") = some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  exact rlpUnchecked_long_string_input_exact checked entered checkedPost output pointer total byte checkedValue uncheckedValue
    checkedPointer checkedTotal atPointer atByte lower upper nonzero checkedCode uncheckedCode ticks uncheckedTicks loaded reads checkedRun bodyRun

#print axioms rlpUnchecked_long_string_body_input_exact

/-- The unchecked whole-function result inherits the checked header input bound. -/
theorem rlpUnchecked_long_list_body_input_exact {F : Type}
    (checked unchecked checkedPost uncheckedPost : PanSemStateFiniteExact 64 F)
    (pointer total : BitVec 64) (byte : UInt8) (checkedValue uncheckedValue : ValueHOL 64)
    (checkedPointer : checked.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (checkedTotal : checked.locals.lookup (ofString "len") = some (.val (.word total)))
    (uncheckedPointer : unchecked.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lower : 247 < byte.toNat) (upper : byte.toNat ≤ 255) (nonzero : total ≠ 0)
    (checkedCode : checked.code = originalRuntimeCode) (uncheckedCode : unchecked.code = originalRuntimeCode)
    (ticks : 11 ≤ checked.clock) (uncheckedTicks : 10 ≤ unchecked.clock)
    (loaded : @panMemLoadByteHOL 64 _ checked.memory checked.memaddrs
      (fun address => Classical.propDecidable (checked.memaddrs address)) checked.be pointer = some byte)
    (reads : ∀ offset : Nat, offset < total.toNat → @panMemLoadByteHOL 64 _ checked.memory checked.memaddrs
        (fun address => Classical.propDecidable (checked.memaddrs address)) checked.be (pointer + BitVec.ofNat 64 offset) =
      @panMemLoadByteHOL 64 _ unchecked.memory unchecked.memaddrs
        (fun address => Classical.propDecidable (unchecked.memaddrs address)) unchecked.be (pointer + BitVec.ofNat 64 offset))
    (checkedRun : evaluateHOLFiniteState checked (sourceFunctionBody Guest.guestFn_rlp_item_header) = (some (.returned checkedValue),checkedPost))
    (uncheckedRun : evaluateHOLFiniteState unchecked (sourceFunctionBody Guest.guestFn_rlp_item_total_unchecked) = (some (.returned uncheckedValue),uncheckedPost)) :
    ∃ headerSize payloadSize kind : BitVec 64,
      checkedValue = .rStruct [.val (.word headerSize),.val (.word payloadSize),.val (.word kind)] ∧
      uncheckedValue = .val (.word (headerSize + payloadSize)) := by
  have totalPositive : 0 < total.toNat := by
    by_contra bad
    apply nonzero
    apply BitVec.eq_of_toNat_eq
    simpa using (show total.toNat = 0 by omega)
  have pointerRead := reads 0 totalPositive
  simp only [BitVec.add_zero] at pointerRead
  have uncheckedLoaded : @panMemLoadByteHOL 64 _ unchecked.memory unchecked.memaddrs
      (fun address => Classical.propDecidable (unchecked.memaddrs address)) unchecked.be pointer = some byte :=
    pointerRead.symm.trans loaded
  obtain ⟨output,bodyRun⟩ := rlpUnchecked_returned_after_load unchecked uncheckedPost pointer byte uncheckedValue uncheckedPointer uncheckedLoaded uncheckedRun
  let entered := setVarHOLFinite (ofString "b") (.val (.word (BitVec.ofNat 64 byte.toNat))) unchecked
  have atPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "b" ≠ ofString "p" by decide] using uncheckedPointer
  have atByte : entered.locals.lookup (ofString "b") = some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  exact rlpUnchecked_long_list_input_exact checked entered checkedPost output pointer total byte checkedValue uncheckedValue
    checkedPointer checkedTotal atPointer atByte lower upper nonzero checkedCode uncheckedCode ticks uncheckedTicks loaded reads checkedRun bodyRun

#print axioms rlpUnchecked_long_list_body_input_exact

end InitECandidate.Runtime
