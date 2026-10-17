import InitECandidate.Runtime.RlpHeaderLongStringFullContract
import InitECandidate.Runtime.RlpHeaderShortStringFullContract
import InitECandidate.Runtime.RlpHeaderLongListFullContract
import InitECandidate.Runtime.RlpHeaderBoundaryCases
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every original item-header execution has a uniform eleven-tick source
clock bound, including empty inputs, unreadable bytes and malformed lengths. -/
theorem evaluate_rlpHeader_uniform_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item_header)
    state.clock ≤ evaluated.2.clock + 11 ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  by_cases empty : length = 0
  · subst length
    have bound := evaluate_rlpHeader_empty_body state lengthLocal code (by omega)
    dsimp only at bound ⊢
    exact ⟨by omega,by omega,bound.2.1,bound.2.2.1⟩
  · cases loaded : @panMemLoadByteHOL 64 _ state.memory state.memaddrs
        (fun address => Classical.propDecidable (state.memaddrs address)) state.be pointer with
    | none =>
      rw [evaluate_rlpHeader_unreadable_header state pointer length pointerLocal lengthLocal empty loaded]
      dsimp only
      exact ⟨by omega,by rfl,by simp,by simp⟩
    | some byte =>
      by_cases single : byte.toNat < 128
      · obtain ⟨post,run,clock,_,_,_⟩ := evaluate_rlpHeader_single_full state pointer length byte
          pointerLocal lengthLocal empty single loaded
        rw [run]
        dsimp only
        exact ⟨by omega,by omega,by simp,by simp⟩
      · by_cases short : byte.toNat ≤ 183
        · obtain ⟨result,post,run,cost,remaining,noTimeout,terminal,_⟩ :=
            evaluate_rlpHeader_short_string_full_contract state pointer length byte pointerLocal lengthLocal
              empty (by omega) short loaded code (by omega)
          rw [run]
          dsimp only
          exact ⟨by omega,remaining,noTimeout,terminal⟩
        · by_cases long : byte.toNat ≤ 191
          · obtain ⟨result,post,run,cost,remaining,noTimeout,terminal⟩ :=
              evaluate_rlpHeader_long_string_full_body_bounded state pointer length byte pointerLocal lengthLocal
                empty (by omega) long loaded code ticks
            rw [run]
            dsimp only
            exact ⟨cost,remaining,noTimeout,terminal⟩
          · by_cases shortList : byte.toNat ≤ 247
            · obtain ⟨result,post,run,cost,remaining,noTimeout,terminal,_⟩ :=
                evaluate_rlpHeader_short_list_full_contract state pointer length byte pointerLocal lengthLocal
                  empty (by omega) shortList loaded code (by omega)
              rw [run]
              dsimp only
              exact ⟨by omega,remaining,noTimeout,terminal⟩
            · have byteBound := byte.toBitVec.isLt
              change byte.toNat < 256 at byteBound
              obtain ⟨result,post,run,cost,remaining,noTimeout,terminal⟩ :=
                evaluate_rlpHeader_long_list_full_body_bounded state pointer length byte pointerLocal lengthLocal
                  empty (by omega) (by omega) loaded code ticks
              rw [run]
              dsimp only
              exact ⟨cost,remaining,noTimeout,terminal⟩

#print axioms evaluate_rlpHeader_uniform_bounded
end InitECandidate.Runtime
