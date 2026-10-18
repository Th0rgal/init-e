import InitECandidate.Runtime.TransactionTypedPathBound
import InitECandidate.Runtime.TransactionTypeGuard
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_type_branch_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length scratch frame : BitVec 64) (ceiling inputLimit : Nat)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (positive : 0 < length.toNat)
    (inputRange : pointer.toNat + length.toNat < 2^64) (lengthBound : length.toNat ≤ inputLimit)
    (limitBound : inputLimit + 9 < 2^64)
    (scratchGlobal : state.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : state.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : state.code = originalRuntimeCode) (orderedFrame : frame ≤ scratch) (framePositive : 0 < frame.toNat)
    (scratchBelow : scratch.toNat ≤ ceiling)
    (arena : ∀ address : BitVec 64, frame.toNat ≤ address.toNat → address.toNat < ceiling → state.memaddrs address)
    (budget : length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92635 ≤ state.clock)
 :
    let output := evaluateHOLFiniteState state transactionTypeParseBranch
    state.clock ≤ output.2.clock + (length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92635) ∧
      output.2.clock ≤ state.clock ∧ output.1 ≠ some .timeOut := by
  have range := transaction_typed_decode_range pointer length positive inputRange
  have factor : (2 * (length - 1).toNat + 1) * 15 + 19 ≤ (2 * length.toNat + 1) * 15 + 19 := by omega
  have product := Nat.mul_le_mul range.2.2.2 factor
  have smaller : (length - 1).toNat * ((2 * (length - 1).toNat + 1) * 15 + 19) + 92635 ≤
      length.toNat * ((2 * length.toNat + 1) * 15 + 19) + 92635 := by omega
  have typed := transaction_typed_path_bounded state pointer length scratch frame ceiling inputLimit pointerLocal lengthLocal positive
    inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena (Nat.le_trans smaller budget)
  have legacy := evaluate_rlpDecodeFully_call_bounded state (some (.local,ofString "top")) transactionLegacyDecodeArguments
    pointer length scratch frame ceiling inputLimit (transaction_legacy_decode_arguments state pointer length pointerLocal lengthLocal)
    inputRange lengthBound limitBound scratchGlobal frameGlobal code orderedFrame framePositive scratchBelow arena budget
  rw [source_transaction_type_branch,evaluateHOLFiniteState_ite]
  split
  · split
    · rw [evaluateHOLFiniteState_ite]
      split
      · split
        · have clock := clockPreserving_of_straightLine (.raise (ofString "TxErr") (.const 2)) (by rfl) state
          have safe := evaluate_straightLine_no_timeout (.raise (ofString "TxErr") (.const 2)) (by rfl) state
          exact ⟨by rw [clock]; omega,Nat.le_of_eq clock,safe⟩
        · rw [source_transaction_legacy_decode]
          exact legacy
      · exact ⟨by change state.clock ≤ state.clock + _; omega,Nat.le_refl _,by simp⟩
    · exact ⟨Nat.le_trans typed.1 (Nat.add_le_add_left smaller _),typed.2⟩
  · exact ⟨by change state.clock ≤ state.clock + _; omega,Nat.le_refl _,by simp⟩

#print axioms transaction_type_branch_bounded
end InitECandidate.Runtime
