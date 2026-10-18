import InitECandidate.Runtime.AuthorizationsStepInputBound
import InitECandidate.Runtime.AuthorizationsLastStoreProgress
import InitECandidate.Runtime.NormalLocalIncrementCalls
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem authorizationStep_increments : NormalLocalIncrement (ofString "i") authorizationStep := by
  rw [source_authorization_step]
  apply normalLocalIncrement_decCall _ _ _ _ _ _ (by decide)
  rw [source_authorization_item_check]
  apply normalLocalIncrement_guard
  rw [source_authorization_inner_slices]
  apply normalLocalIncrement_decCall _ _ _ _ _ _ (by decide)
  rw [source_authorization_entry_check]
  apply normalLocalIncrement_guard
  rw [source_authorization_record_scope]
  apply normalLocalIncrement_dec _ _ _ _ _ (by decide)
  rw [source_authorization_cid_declaration]
  apply normalLocalIncrement_decCall _ _ _ _ _ _ (by decide)
  rw [source_authorization_cid_store]
  apply normalLocalIncrement_seq _ _ _ (by rfl)
  rw [source_authorization_address_declaration]
  apply normalLocalIncrement_decCall _ _ _ _ _ _ (by decide)
  rw [source_authorization_address_store]
  apply normalLocalIncrement_seq _ _ _ (by rfl)
  rw [source_authorization_word2_declaration]
  apply normalLocalIncrement_decCall _ _ _ _ _ _ (by decide)
  rw [source_authorization_word2_store]
  apply normalLocalIncrement_seq _ _ _ (by rfl)
  rw [source_authorization_word_assignment]
  apply normalLocalIncrement_localCall _ _ _ _ _ (by decide)
  rw [source_authorization_word_store_and_rs]
  apply normalLocalIncrement_seq _ _ _ (by rfl)
  rw [source_authorization_r_scalar]
  apply normalLocalIncrement_decCall _ _ _ _ _ _ (by decide)
  rw [source_authorization_r_store_and_last]
  apply normalLocalIncrement_seq _ _ _ (by rfl)
  rw [source_authorization_last_scalar]
  apply normalLocalIncrement_decCall _ _ _ _ _ _ (by decide)
  exact authorizationLastStore_increments

def authorizationRank {F : Type} (count : BitVec 64) (state : PanSemStateFiniteExact 64 F) : Nat :=
  match state.locals.lookup (ofString "i") with
  | some (.val (.word index)) => count.toNat - index.toNat
  | _ => 0

/-- Every normally completed actual iteration advances without modular wrap
while inside the outer list, and strictly decreases its remaining-entry rank. -/
theorem evaluate_authorization_step_rank_progress {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (index count : BitVec 64)
    (binding : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (inside : index.toNat < count.toNat)
    (run : evaluateHOLFiniteState state authorizationStep = (none,post)) :
    post.locals.lookup (ofString "i") = some (.val (.word (index + 1))) ∧
      (index + 1).toNat = index.toNat + 1 ∧ authorizationRank count post < authorizationRank count state := by
  have advanced := authorizationStep_increments state post index binding run
  have nextNat : (index + 1).toNat = index.toNat + 1 := by
    rw [BitVec.toNat_add_of_lt (by have limit := count.isLt; change index.toNat + 1 < 2^64; omega)]
    rfl
  refine ⟨advanced,nextNat,?_⟩
  simp only [authorizationRank,binding,advanced]
  rw [nextNat]
  omega

#print axioms authorizationStep_increments
#print axioms evaluate_authorization_step_rank_progress
end InitECandidate.Runtime
