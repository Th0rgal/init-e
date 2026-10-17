import InitECandidate.Runtime.RlpUncheckedBodyInputExact
import InitECandidate.Runtime.RlpItemTotalReturnedHeaderExact
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpUnchecked_item_total_input_equal {F : Type}
    (checked unchecked checkedPost uncheckedPost : PanSemStateFiniteExact 64 F)
    (pointer total : BitVec 64) (byte : UInt8) (checkedValue uncheckedValue : ValueHOL 64)
    (checkedPointer : checked.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (checkedTotal : checked.locals.lookup (ofString "len") = some (.val (.word total)))
    (uncheckedPointer : unchecked.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (nonzero : total ≠ 0)
    (checkedCode : checked.code = originalRuntimeCode) (uncheckedCode : unchecked.code = originalRuntimeCode)
    (ticks : 12 ≤ checked.clock) (uncheckedTicks : 10 ≤ unchecked.clock)
    (loaded : @panMemLoadByteHOL 64 _ checked.memory checked.memaddrs
      (fun address => Classical.propDecidable (checked.memaddrs address)) checked.be pointer = some byte)
    (reads : ∀ offset : Nat, offset < total.toNat → @panMemLoadByteHOL 64 _ checked.memory checked.memaddrs
        (fun address => Classical.propDecidable (checked.memaddrs address)) checked.be (pointer + BitVec.ofNat 64 offset) =
      @panMemLoadByteHOL 64 _ unchecked.memory unchecked.memaddrs
        (fun address => Classical.propDecidable (unchecked.memaddrs address)) unchecked.be (pointer + BitVec.ofNat 64 offset))
    (checkedRun : evaluateHOLFiniteState checked (sourceFunctionBody Guest.guestFn_rlp_item_total) = (some (.returned checkedValue),checkedPost))
    (uncheckedRun : evaluateHOLFiniteState unchecked (sourceFunctionBody Guest.guestFn_rlp_item_total_unchecked) = (some (.returned uncheckedValue),uncheckedPost)) :
    checkedValue = uncheckedValue := by
  obtain ⟨header,payload,kind,headerPost,headerRun,checkedSize⟩ := rlpItemTotal_body_returned_header_exact checked checkedPost pointer total checkedValue
    checkedPointer checkedTotal checkedCode ticks checkedRun
  let entry := callEntryStateHOLFinite checked (rlpHeaderCallee pointer total)
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word total)) := by
    simp [entry,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨otherHeader,otherPayload,otherKind,shape,uncheckedSize⟩ := rlpUnchecked_body_input_exact entry unchecked headerPost uncheckedPost pointer total byte
    (.rStruct [.val (.word header),.val (.word payload),.val (.word kind)]) uncheckedValue
    atPointer atLength uncheckedPointer nonzero checkedCode uncheckedCode (by change 11 ≤ checked.clock - 1; omega)
    uncheckedTicks loaded reads headerRun uncheckedRun
  have fields : header = otherHeader ∧ payload = otherPayload ∧ kind = otherKind := by
    simpa using shape
  rw [checkedSize,uncheckedSize,fields.1,fields.2.1]

#print axioms rlpUnchecked_item_total_input_equal
end InitECandidate.Runtime
