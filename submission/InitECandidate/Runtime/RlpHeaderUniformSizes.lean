import InitECandidate.Runtime.RlpHeaderUniformResult
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Adding the prefix byte to at most eight length bytes cannot wrap. -/
theorem rlpHeader_long_header_word_bounds (lengthBytes : BitVec 64) (small : lengthBytes.toNat ≤ 8) :
    (1 + lengthBytes).toNat ≤ 9 ∧ 0 < (1 + lengthBytes).toNat := by
  have natural : (1 + lengthBytes).toNat = 1 + lengthBytes.toNat := by
    rw [BitVec.toNat_add_of_lt (by change 1 + lengthBytes.toNat < 2^64; omega)]
    rfl
  rw [natural]
  omega

/-- Every successful original header has at most nine prefix bytes, an
input-bounded payload and a positive prefix whenever it denotes a list. -/
theorem rlpHeader_uniform_return_sizes {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item_header) = (some (.returned value),post)) :
    ∃ header payload kind : BitVec 64,
      value = .rStruct [.val (.word header),.val (.word payload),.val (.word kind)] ∧
      header.toNat ≤ 9 ∧ payload.toNat ≤ length.toNat ∧ (kind = 1 → 0 < header.toNat) := by
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
        exact ⟨0,1,0,shape,by decide,positive,by intro impossible; contradiction⟩
      · by_cases short : byte.toNat ≤ 183
        · obtain ⟨result,output,actual,_,_,_,_,returned,_⟩ :=
            evaluate_rlpHeader_short_string_full_contract state pointer length byte pointerLocal lengthLocal
              empty (by omega) short loaded code (by omega)
          have equal := (Prod.mk.inj (actual.symm.trans run)).1
          obtain ⟨shape,smaller,positive,bounded⟩ := returned value equal
          exact ⟨1,(BitVec.ofNat 64 byte.toNat) - 128,0,shape,by decide,by omega,
            by intro impossible; contradiction⟩
        · by_cases long : byte.toNat ≤ 191
          · obtain ⟨payload,shape,smaller,positive,bounded⟩ := rlpHeader_long_string_full_return_contract state post
              pointer length byte value pointerLocal lengthLocal empty (by omega) long loaded code ticks run
            have lengthBounds := rlp_long_string_length_bytes (BitVec.ofNat 64 byte.toNat)
              (by change 183 < byte.toNat % 2^64; omega) (by change byte.toNat % 2^64 ≤ 191; omega)
            have headerBounds := rlpHeader_long_header_word_bounds _ lengthBounds.2
            exact ⟨1 + ((BitVec.ofNat 64 byte.toNat) - 183),payload,0,shape,headerBounds.1,
              by omega,by intro impossible; contradiction⟩
          · by_cases shortList : byte.toNat ≤ 247
            · obtain ⟨result,output,actual,_,_,_,_,returned,_⟩ :=
                evaluate_rlpHeader_short_list_full_contract state pointer length byte pointerLocal lengthLocal
                  empty (by omega) shortList loaded code (by omega)
              have equal := (Prod.mk.inj (actual.symm.trans run)).1
              obtain ⟨shape,smaller,positive,bounded⟩ := returned value equal
              exact ⟨1,(BitVec.ofNat 64 byte.toNat) - 192,1,shape,by decide,by omega,by intro; decide⟩
            · have byteBound := byte.toBitVec.isLt
              change byte.toNat < 256 at byteBound
              obtain ⟨payload,shape,smaller,positive,bounded⟩ := rlpHeader_long_list_full_return_contract state post
                pointer length byte value pointerLocal lengthLocal empty (by omega) (by omega) loaded code ticks run
              have lengthBounds := rlp_long_list_length_bytes byte (by change 247 < byte.toNat % 2^64; omega)
              have headerBounds := rlpHeader_long_header_word_bounds _ lengthBounds.2
              exact ⟨1 + ((BitVec.ofNat 64 byte.toNat) - 247),payload,1,shape,headerBounds.1,
                by omega,by intro; exact headerBounds.2⟩

/-- Header size facts apply to the actual returned fields, rather than only
to existential witnesses for a successful result. -/
theorem rlpHeader_uniform_return_field_sizes {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length header payload kind : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item_header) =
      (some (.returned (.rStruct [.val (.word header),.val (.word payload),.val (.word kind)])),post)) :
    header.toNat ≤ 9 ∧ payload.toNat ≤ length.toNat ∧ (kind = 1 → 0 < header.toNat) := by
  obtain ⟨actualHeader,actualPayload,actualKind,shape,small,bounded,positive⟩ :=
    rlpHeader_uniform_return_sizes state post pointer length _ pointerLocal lengthLocal code ticks run
  simp only [ValueHOL.rStruct.injEq,List.cons.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq,and_true] at shape
  obtain ⟨rfl,rfl,rfl⟩ := shape
  exact ⟨small,bounded,positive⟩

#print axioms rlpHeader_uniform_return_field_sizes
#print axioms rlpHeader_long_header_word_bounds
#print axioms rlpHeader_uniform_return_sizes
end InitECandidate.Runtime
