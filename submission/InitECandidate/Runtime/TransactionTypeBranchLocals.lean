import InitECandidate.Runtime.TransactionTypedPathLocals
import InitECandidate.Runtime.TransactionTypeGuard
import InitECandidate.Runtime.TrapBodyClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem transaction_type_branch_normal_type_count {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (byte : BitVec 64)
    (typeLocal : state.locals.lookup (ofString "t") = some (.val (.word (0 : BitVec 64))))
    (byteLocal : state.locals.lookup (ofString "b0") = some (.val (.word byte)))
    (countLocal : state.locals.lookup (ofString "nfields") = some (.val (.word (9 : BitVec 64))))
    (run : evaluateHOLFiniteState state transactionTypeParseBranch = (none,post)) :
    ∃ kind : BitVec 64, (kind = 0 ∨ kind = 1 ∨ kind = 2 ∨ kind = 3 ∨ kind = 4) ∧
      post.locals.lookup (ofString "t") = some (.val (.word kind)) ∧
      post.locals.lookup (ofString "nfields") = some (.val (.word (BitVec.ofNat 64 (transactionRequiredFields kind)))) := by
  rw [source_transaction_type_branch,evaluateHOLFiniteState_ite,
    evaluate_transaction_byte_range state byte 1 4 byteLocal] at run
  by_cases typed : ¬ byte < (1 : BitVec 64) ∧ ¬ (4 : BitVec 64) < byte
  · rw [if_pos typed] at run
    dsimp only at run
    rw [if_neg (by decide : (1 : BitVec 64) ≠ 0)] at run
    have supported := transaction_typed_guard_supported byte typed.1 typed.2
    obtain ⟨typePost,countPost⟩ := transaction_typed_path_normal_type_count state post byte 0 supported typeLocal byteLocal countLocal run
    exact ⟨byte,supported,typePost,countPost⟩
  · rw [if_neg typed] at run
    dsimp only at run
    rw [if_pos (rfl : (0 : BitVec 64) = 0),evaluateHOLFiniteState_ite] at run
    split at run
    · split at run
      · have terminal := evaluate_raise_terminal state (ofString "TxErr") (.const 2)
        rw [run] at terminal
        exact False.elim (terminal rfl)
      · have atType := evaluate_normalLocalFrame (ofString "t") transactionLegacyPath (by rw [source_transaction_legacy_decode]; rfl) state post run
        have atCount := evaluate_normalLocalFrame (ofString "nfields") transactionLegacyPath (by rw [source_transaction_legacy_decode]; rfl) state post run
        exact ⟨0,Or.inl rfl,atType.trans typeLocal,by simpa [transactionRequiredFields] using atCount.trans countLocal⟩
    · cases run

#print axioms transaction_type_branch_normal_type_count
end InitECandidate.Runtime
