import InitECandidate.Runtime.RlpItemShortFullProgress
import InitECandidate.Runtime.RlpItemLongFullContract
import InitECandidate.Runtime.RlpItemShortListFullReturn
import InitECandidate.Runtime.RlpItemLongListFullReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Common successful item shape and input-bounded progress for every header class. -/
def RlpItemProgress (value : ValueHOL 64) (total : BitVec 64) : Prop :=
  ∃ kind pointer payload consumed : BitVec 64,
    value = .rStruct [.val (.word kind),.val (.word pointer),.val (.word payload),.val (.word consumed)] ∧
      (kind = 0 ∨ kind = 1) ∧ payload.toNat ≤ total.toNat ∧
      0 < consumed.toNat ∧ consumed.toNat ≤ total.toNat

/-- All five original header paths satisfy one return contract after a
successful first-byte load. No payload-memory readability premise is needed. -/
theorem rlpItem_loaded_return_progress {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer total : BitVec 64) (byte : UInt8) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (nonzero : total ≠ 0)
    (loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
      (fun address => Classical.propDecidable (state.memaddrs address)) state.be pointer = some byte)
    (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item) = (some (.returned value),post)) :
    RlpItemProgress value total := by
  by_cases single : byte.toNat < 128
  · obtain ⟨output,actual,_⟩ := evaluate_rlpItem_single_byte_body state pointer total byte
      pointerLocal totalLocal nonzero single loaded
    have equal := (Prod.mk.inj (run.symm.trans actual)).1
    have positive : 1 ≤ total.toNat := by
      by_contra bad
      apply nonzero
      apply BitVec.eq_of_toNat_eq
      simpa using (show total.toNat = 0 by omega)
    refine ⟨0,pointer,1,1,?_,Or.inl rfl,?_,by decide,?_⟩
    · simpa using equal
    · exact positive
    · exact positive
  by_cases short : byte.toNat ≤ 183
  · obtain ⟨result,output,actual,_,_,_,_,fields,_⟩ := evaluate_rlpItem_short_full_body state pointer total byte
      pointerLocal totalLocal nonzero (by omega) short loaded code (by omega)
    have same := Prod.mk.inj (actual.symm.trans run)
    have exactFields := fields value same.1
    have progress := rlpItem_short_full_return_progress state post pointer total byte value
      pointerLocal totalLocal nonzero (by omega) short loaded code (by omega) run
    exact ⟨0,pointer+1,(BitVec.ofNat 64 byte.toNat)-128,1+((BitVec.ofNat 64 byte.toNat)-128),
      exactFields,Or.inl rfl,by omega,progress.2⟩
  by_cases longString : byte.toNat ≤ 191
  · obtain ⟨payload,fields,small,positive,bounded⟩ := rlpItem_long_full_return_contract state post pointer total byte value
      pointerLocal totalLocal nonzero (by omega) longString loaded code ticks run
    exact ⟨0,pointer+(1+((BitVec.ofNat 64 byte.toNat)-183)),payload,
      1+(((BitVec.ofNat 64 byte.toNat)-183)+payload),fields,Or.inl rfl,by omega,positive,bounded⟩
  by_cases shortList : byte.toNat ≤ 247
  · obtain ⟨fields,small,positive,bounded⟩ := rlpItem_short_list_full_return_contract state post pointer total byte value
      pointerLocal loaded totalLocal (by omega) shortList nonzero code (by omega) run
    exact ⟨1,pointer+1,(BitVec.ofNat 64 byte.toNat)-192,1+((BitVec.ofNat 64 byte.toNat)-192),
      fields,Or.inr rfl,by omega,positive,bounded⟩
  · have byteBound := byte.toNat_lt_size
    change byte.toNat < 256 at byteBound
    obtain ⟨payload,fields,small,positive,bounded⟩ := rlpItem_long_list_full_return_contract state post pointer total byte value
      pointerLocal loaded totalLocal (by omega) (by omega) nonzero code (by omega) run
    exact ⟨1,pointer+(1+((BitVec.ofNat 64 byte.toNat)-247)),payload,
      1+(((BitVec.ofNat 64 byte.toNat)-247)+payload),fields,Or.inr rfl,by omega,positive,bounded⟩

#print axioms rlpItem_loaded_return_progress
end InitECandidate.Runtime
