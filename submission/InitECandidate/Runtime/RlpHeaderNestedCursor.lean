import InitECandidate.Runtime.RlpHeaderUniformSizes
import InitECandidate.Runtime.RlpValidationNestedGeometry
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful list-header execution supplies the actual nested cursor
ordering used by the validator, with no header-size or positivity assumptions. -/
theorem rlpHeader_returned_list_cursor {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (position stop header payload : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word position)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word (stop - position))))
    (ordered : position.toNat ≤ stop.toNat)
    (inputBound : (stop - position).toNat + 9 < 2^64)
    (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item_header) =
      (some (.returned (.rStruct [.val (.word header),.val (.word payload),.val (.word 1)])),post)) :
    position.toNat < (position + header).toNat ∧
      (position + header).toNat ≤ (position + header + payload).toNat ∧
      (position + header + payload).toNat ≤ stop.toNat ∧ payload.toNat < (stop - position).toNat := by
  have sizes := rlpHeader_uniform_return_field_sizes state post position (stop - position) header payload 1
    pointerLocal lengthLocal code ticks run
  obtain ⟨actualHeader,actualPayload,kind,shape,_,positive,bounded,nested⟩ :=
    rlpHeader_uniform_return_progress state post position (stop - position) _ pointerLocal lengthLocal code ticks run
  simp only [ValueHOL.rStruct.injEq,List.cons.injEq,ValueHOL.val.injEq,HolWordLab.word.injEq,and_true] at shape
  obtain ⟨rfl,rfl,rfl⟩ := shape
  have geometry := rlpValidation_nested_geometry position stop header payload ordered (sizes.2.2 rfl)
    (rlpValidation_header_payload_no_wrap header payload (stop - position) sizes.1 sizes.2.1 inputBound) bounded
  exact ⟨geometry.1,geometry.2.1,geometry.2.2,nested rfl⟩

/-- The rank decreases directly from the original successful list-header run. -/
theorem rlpHeader_returned_list_rank {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (position stop header payload record : BitVec 64) (frames : List RlpValidationFrame)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word position)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word (stop - position))))
    (ordered : position.toNat ≤ stop.toNat)
    (inputBound : (stop - position).toNat + 9 < 2^64)
    (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item_header) =
      (some (.returned (.rStruct [.val (.word header),.val (.word payload),.val (.word 1)])),post)) :
    rlpValidationRank (position + header) (position + header + payload)
      ({record := record,resume := position + header + payload,stop := stop} :: frames) <
      rlpValidationRank position stop frames := by
  have geometry := rlpHeader_returned_list_cursor state post position stop header payload
    pointerLocal lengthLocal ordered inputBound code ticks run
  exact rlpValidation_rank_push position (position + header) (position + header + payload) stop record frames
    geometry.1 geometry.2.1 geometry.2.2.1

#print axioms rlpHeader_returned_list_rank
#print axioms rlpHeader_returned_list_cursor
end InitECandidate.Runtime
