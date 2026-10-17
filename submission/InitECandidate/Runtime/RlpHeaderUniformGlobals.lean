import InitECandidate.Runtime.RlpHeaderLongStringFullGlobals
import InitECandidate.Runtime.RlpHeaderLongListFullGlobals
import InitECandidate.Runtime.RlpHeaderUniformResult
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every successful original item-header execution preserves globals across
all byte cases, including the nested length-reader calls in long headers. -/
theorem rlpHeader_uniform_returned_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item_header) = (some (.returned value),post)) :
    post.globals = state.globals := by
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
      · obtain ⟨output,actual,_,_,globals,_⟩ := evaluate_rlpHeader_single_full state pointer length byte
          pointerLocal lengthLocal empty single loaded
        have same := (Prod.mk.inj (actual.symm.trans run)).2
        rw [← same]
        exact globals
      · by_cases short : byte.toNat ≤ 183
        · obtain ⟨result,output,actual,_,_,_,_,_,_,globals⟩ := evaluate_rlpHeader_short_string_full_contract
            state pointer length byte pointerLocal lengthLocal empty (by omega) short loaded code (by omega)
          have same := (Prod.mk.inj (actual.symm.trans run)).2
          rw [← same]
          exact globals
        · by_cases long : byte.toNat ≤ 191
          · exact rlpHeader_long_string_full_returned_globals state post pointer length byte value pointerLocal lengthLocal
              empty (by omega) long loaded code ticks run
          · by_cases shortList : byte.toNat ≤ 247
            · obtain ⟨result,output,actual,_,_,_,_,_,_,globals⟩ := evaluate_rlpHeader_short_list_full_contract
                state pointer length byte pointerLocal lengthLocal empty (by omega) shortList loaded code (by omega)
              have same := (Prod.mk.inj (actual.symm.trans run)).2
              rw [← same]
              exact globals
            · have byteBound := byte.toBitVec.isLt
              change byte.toNat < 256 at byteBound
              exact rlpHeader_long_list_full_returned_globals state post pointer length byte value pointerLocal lengthLocal
                empty (by omega) (by omega) loaded code run

#print axioms rlpHeader_uniform_returned_globals
end InitECandidate.Runtime
