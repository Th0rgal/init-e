import InitECandidate.Runtime.RlpHeaderUniformBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The common successful header shape and progress needed by item traversal. -/
def RlpHeaderProgress (value : ValueHOL 64) (length : BitVec 64) : Prop :=
  ∃ header payload kind : BitVec 64,
    value = .rStruct [.val (.word header),.val (.word payload),.val (.word kind)] ∧
    (kind = 0 ∨ kind = 1) ∧ 0 < (header + payload).toNat ∧
    (header + payload).toNat ≤ length.toNat ∧ (kind = 1 → payload.toNat < length.toNat)

/-- Every successful original header result has the common three-word shape,
positive input-bounded consumption and strictly smaller nested-list payload. -/
theorem rlpHeader_uniform_return_progress {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item_header) = (some (.returned value),post)) :
    RlpHeaderProgress value length := by
  by_cases empty : length = 0
  · subst length
    have bound := evaluate_rlpHeader_empty_body state lengthLocal code (by omega)
    rw [run] at bound
    exact False.elim (bound.2.2.2 value rfl)
  · cases loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
        (fun address => Classical.propDecidable (state.memaddrs address)) state.be pointer with
    | none =>
      have stopped := evaluate_rlpHeader_unreadable_header state pointer length pointerLocal lengthLocal empty loaded
      rw [run] at stopped
      cases stopped
    | some byte =>
      by_cases single : byte.toNat < 128
      · obtain ⟨output,actual,_,_,_,positive⟩ := evaluate_rlpHeader_single_full state pointer length byte
          pointerLocal lengthLocal empty single loaded
        have shape : value = rlpHeaderSingleValue :=
          PanSemResultExact.returned.inj (Option.some.inj (Prod.mk.inj (run.symm.trans actual)).1)
        exact ⟨0,1,0,shape,Or.inl rfl,by decide,positive,by intro impossible; contradiction⟩
      · by_cases short : byte.toNat ≤ 183
        · obtain ⟨result,output,actual,_,_,_,_,returned,_⟩ :=
            evaluate_rlpHeader_short_string_full_contract state pointer length byte pointerLocal lengthLocal
              empty (by omega) short loaded code (by omega)
          have equal := (Prod.mk.inj (actual.symm.trans run)).1
          obtain ⟨shape,_,positive,bounded⟩ := returned value equal
          exact ⟨1,(BitVec.ofNat 64 byte.toNat) - 128,0,shape,Or.inl rfl,positive,bounded,
            by intro impossible; contradiction⟩
        · by_cases long : byte.toNat ≤ 191
          · obtain ⟨payload,shape,_,positive,bounded⟩ := rlpHeader_long_string_full_return_contract state post
              pointer length byte value pointerLocal lengthLocal empty (by omega) long loaded code ticks run
            refine ⟨1 + ((BitVec.ofNat 64 byte.toNat) - 183),payload,0,shape,Or.inl rfl,?_,?_,?_⟩
            · simpa only [BitVec.add_assoc] using positive
            · simpa only [BitVec.add_assoc] using bounded
            · intro impossible; contradiction
          · by_cases shortList : byte.toNat ≤ 247
            · obtain ⟨result,output,actual,_,_,_,_,returned,_⟩ :=
                evaluate_rlpHeader_short_list_full_contract state pointer length byte pointerLocal lengthLocal
                  empty (by omega) shortList loaded code (by omega)
              have equal := (Prod.mk.inj (actual.symm.trans run)).1
              obtain ⟨shape,smaller,positive,bounded⟩ := returned value equal
              exact ⟨1,(BitVec.ofNat 64 byte.toNat) - 192,1,shape,Or.inr rfl,positive,bounded,by intro; exact smaller⟩
            · have byteBound := byte.toBitVec.isLt
              change byte.toNat < 256 at byteBound
              obtain ⟨payload,shape,smaller,positive,bounded⟩ := rlpHeader_long_list_full_return_contract state post
                pointer length byte value pointerLocal lengthLocal empty (by omega) (by omega) loaded code ticks run
              refine ⟨1 + ((BitVec.ofNat 64 byte.toNat) - 247),payload,1,shape,Or.inr rfl,?_,?_,?_⟩
              · simpa only [BitVec.add_assoc] using positive
              · simpa only [BitVec.add_assoc] using bounded
              · intro; exact smaller

/-- Uniform caller-facing header contract covering every input and result. -/
theorem evaluate_rlpHeader_uniform_contract {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item_header) = (result,post) ∧
      state.clock ≤ post.clock + 11 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧ result ≠ none ∧
      (∀ value, result = some (.returned value) → RlpHeaderProgress value length) := by
  have bound := evaluate_rlpHeader_uniform_bounded state pointer length pointerLocal lengthLocal code ticks
  cases run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item_header) with
  | mk result post =>
    rw [run] at bound
    refine ⟨result,post,rfl,bound.1,bound.2.1,bound.2.2.1,bound.2.2.2,?_⟩
    intro value equal
    exact rlpHeader_uniform_return_progress state post pointer length value pointerLocal lengthLocal code ticks
      (by rw [run]; exact congrArg (fun result => (result,post)) equal)

#print axioms evaluate_rlpHeader_uniform_contract
#print axioms rlpHeader_uniform_return_progress
end InitECandidate.Runtime
