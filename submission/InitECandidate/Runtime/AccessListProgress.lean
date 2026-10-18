import InitECandidate.Runtime.DiscardCallSuccessLocals
import InitECandidate.Runtime.AccessListSource
import InitECandidate.Runtime.NormalLocalIncrementCalls
import InitECandidate.Runtime.NormalLocalFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem accessKeysStep_increments : NormalLocalIncrement (ofString "j") accessKeysStep := by
  rw [source_access_keys_step]
  apply normalLocalIncrement_decCall _ _ _ _ _ _ (by decide)
  rw [source_access_keys_copy]
  apply normalLocalIncrement_seq_normal_frame
  · intro F state post run
    have same := evaluate_discard_call_success_locals state (ofString "memcpy") _ (by rw [run])
    rw [run] at same
    exact congrArg (fun locals => locals.lookup (ofString "j")) same
  · exact normalLocalIncrement_assign _

/-- Actual successful key iterations advance without wrap while inside their list. -/
theorem access_keys_step_progress {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (index count : BitVec 64)
    (binding : state.locals.lookup (ofString "j") = some (.val (.word index)))
    (inside : index.toNat < count.toNat)
    (run : evaluateHOLFiniteState state accessKeysStep = (none,post)) :
    post.locals.lookup (ofString "j") = some (.val (.word (index + 1))) ∧
      (index + 1).toNat = index.toNat + 1 := by
  refine ⟨accessKeysStep_increments state post index binding run,?_⟩
  rw [BitVec.toNat_add_of_lt (by have limit := count.isLt; change index.toNat + 1 < 2^64; omega)]
  rfl

#print axioms accessKeysStep_increments
#print axioms access_keys_step_progress
end InitECandidate.Runtime
