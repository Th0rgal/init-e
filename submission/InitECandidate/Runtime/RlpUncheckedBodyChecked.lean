import InitECandidate.Runtime.RlpUncheckedSingleBodyChecked
import InitECandidate.Runtime.RlpUncheckedShortStringBodyChecked
import InitECandidate.Runtime.RlpUncheckedShortListBodyChecked
import InitECandidate.Runtime.RlpUncheckedLongBodyChecked
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpUnchecked_body_checked_bound {F : Type}
    (checked unchecked checkedPost uncheckedPost : PanSemStateFiniteExact 64 F)
    (pointer total : BitVec 64) (byte : UInt8) (checkedValue uncheckedValue : ValueHOL 64)
    (checkedPointer : checked.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (checkedTotal : checked.locals.lookup (ofString "len") = some (.val (.word total)))
    (uncheckedPointer : unchecked.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (nonzero : total ≠ 0)
    (checkedCode : checked.code = originalRuntimeCode) (uncheckedCode : unchecked.code = originalRuntimeCode)
    (ticks : 11 ≤ checked.clock) (uncheckedTicks : 10 ≤ unchecked.clock)
    (loaded : @panMemLoadByteHOL 64 _ checked.memory checked.memaddrs
      (fun address => Classical.propDecidable (checked.memaddrs address)) checked.be pointer = some byte)
    (reads : ∀ address, @panMemLoadByteHOL 64 _ checked.memory checked.memaddrs
        (fun address => Classical.propDecidable (checked.memaddrs address)) checked.be address =
      @panMemLoadByteHOL 64 _ unchecked.memory unchecked.memaddrs
        (fun address => Classical.propDecidable (unchecked.memaddrs address)) unchecked.be address)
    (checkedRun : evaluateHOLFiniteState checked (sourceFunctionBody Guest.guestFn_rlp_item_header) = (some (.returned checkedValue),checkedPost))
    (uncheckedRun : evaluateHOLFiniteState unchecked (sourceFunctionBody Guest.guestFn_rlp_item_total_unchecked) = (some (.returned uncheckedValue),uncheckedPost)) :
    ∃ consumed : BitVec 64, uncheckedValue = .val (.word consumed) ∧ 0 < consumed.toNat ∧ consumed.toNat ≤ total.toNat := by
  by_cases single : byte.toNat < 128
  · exact rlpUnchecked_single_body_checked_bound checked unchecked checkedPost uncheckedPost pointer total byte checkedValue uncheckedValue
      checkedPointer checkedTotal uncheckedPointer single nonzero checkedCode uncheckedCode ticks uncheckedTicks loaded reads checkedRun uncheckedRun
  by_cases shortString : byte.toNat ≤ 183
  · exact rlpUnchecked_short_string_body_checked_bound checked unchecked checkedPost uncheckedPost pointer total byte checkedValue uncheckedValue
      checkedPointer checkedTotal uncheckedPointer (by omega) shortString nonzero checkedCode uncheckedCode ticks uncheckedTicks loaded reads checkedRun uncheckedRun
  by_cases longString : byte.toNat ≤ 191
  · exact rlpUnchecked_long_string_body_checked_bound checked unchecked checkedPost uncheckedPost pointer total byte checkedValue uncheckedValue
      checkedPointer checkedTotal uncheckedPointer (by omega) longString nonzero checkedCode uncheckedCode ticks uncheckedTicks loaded reads checkedRun uncheckedRun
  by_cases shortList : byte.toNat ≤ 247
  · exact rlpUnchecked_short_list_body_checked_bound checked unchecked checkedPost uncheckedPost pointer total byte checkedValue uncheckedValue
      checkedPointer checkedTotal uncheckedPointer (by omega) shortList nonzero checkedCode uncheckedCode ticks uncheckedTicks loaded reads checkedRun uncheckedRun
  have byteBound : byte.toNat ≤ 255 := by have bound := byte.toBitVec.isLt; change byte.toNat < 256 at bound; omega
  exact rlpUnchecked_long_list_body_checked_bound checked unchecked checkedPost uncheckedPost pointer total byte checkedValue uncheckedValue
    checkedPointer checkedTotal uncheckedPointer (by omega) byteBound nonzero checkedCode uncheckedCode ticks uncheckedTicks loaded reads checkedRun uncheckedRun

#print axioms rlpUnchecked_body_checked_bound
end InitECandidate.Runtime
