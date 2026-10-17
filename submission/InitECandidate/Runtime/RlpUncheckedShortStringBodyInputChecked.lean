import InitECandidate.Runtime.RlpUncheckedReturnedAfterLoad
import InitECandidate.Runtime.RlpUncheckedShortValue
import InitECandidate.Runtime.RlpHeaderShortStringFullContract
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpUnchecked_short_string_body_input_checked_bound {F : Type}
    (checked unchecked checkedPost uncheckedPost : PanSemStateFiniteExact 64 F)
    (pointer total : BitVec 64) (byte : UInt8) (checkedValue uncheckedValue : ValueHOL 64)
    (checkedPointer : checked.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (checkedTotal : checked.locals.lookup (ofString "len") = some (.val (.word total)))
    (uncheckedPointer : unchecked.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lower : 128 ≤ byte.toNat) (upper : byte.toNat ≤ 183) (nonzero : total ≠ 0)
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
    ∃ consumed : BitVec 64, uncheckedValue = .val (.word consumed) ∧ 0 < consumed.toNat ∧ consumed.toNat ≤ total.toNat := by
  have totalPositive : 0 < total.toNat := by
    by_contra bad
    apply nonzero
    apply BitVec.eq_of_toNat_eq
    simpa using (show total.toNat = 0 by omega)
  have pointerRead := reads 0 totalPositive
  simp only [BitVec.add_zero] at pointerRead
  obtain ⟨result,post,run,_,_,_,_,returned,_,_⟩ := evaluate_rlpHeader_short_string_full_contract checked pointer total byte
    checkedPointer checkedTotal nonzero lower upper loaded checkedCode (by omega)
  have same := Prod.mk.inj (run.symm.trans checkedRun)
  have progress := returned checkedValue same.1
  have uncheckedLoaded := pointerRead.symm.trans loaded
  obtain ⟨output,bodyRun⟩ := rlpUnchecked_returned_after_load unchecked uncheckedPost pointer byte uncheckedValue uncheckedPointer uncheckedLoaded uncheckedRun
  let entered := setVarHOLFinite (ofString "b") (.val (.word (BitVec.ofNat 64 byte.toNat))) unchecked
  have atByte : entered.locals.lookup (ofString "b") = some (.val (.word (BitVec.ofNat 64 byte.toNat))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have low : 128 ≤ (BitVec.ofNat 64 byte.toNat).toNat := by change 128 ≤ byte.toNat % 2^64; omega
  have high : (BitVec.ofNat 64 byte.toNat).toNat ≤ 183 := by change byte.toNat % 2^64 ≤ 183; omega
  have notSingle : ¬(BitVec.ofNat 64 byte.toNat).toNat < 128 := by omega
  have exactRun := evaluate_rlpUnchecked_short_after_load entered (BitVec.ofNat 64 byte.toNat) atByte high
  simp only [if_neg notSingle] at exactRun
  have equal := (Prod.mk.inj (bodyRun.symm.trans exactRun)).1
  have valueEq : uncheckedValue = .val (.word ((1 + BitVec.ofNat 64 byte.toNat) - 128)) := by
    cases equal
    rfl
  have algebra : ((1 : BitVec 64) + BitVec.ofNat 64 byte.toNat) - 128 = 1 + (BitVec.ofNat 64 byte.toNat - 128) := by
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]
  refine ⟨(1 + BitVec.ofNat 64 byte.toNat) - 128,valueEq,?_,?_⟩
  · rw [algebra]; exact progress.2.2.1
  · rw [algebra]; exact progress.2.2.2

#print axioms rlpUnchecked_short_string_body_input_checked_bound
end InitECandidate.Runtime
