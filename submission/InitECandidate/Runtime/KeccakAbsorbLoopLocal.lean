import InitECandidate.Runtime.KeccakAbsorbLoops
import InitECandidate.Runtime.StoreAdvance8LoopLocal
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Both original absorption loops use at most seventeen source ticks,
including inaccessible or non-word memory causing an early error. -/
theorem evaluate_keccakAbsorb_loop_choice_local {F : Type} (state : PanSemStateFiniteExact 64 F)
    (initial : state.locals.lookup (ofString "i") = some (.val (.word (0 : BitVec 64))))
    (name : MlS) (different : name ≠ ofString "i")
    (ticks : 17 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state keccakAbsorbChoice = (result,post) ∧
      state.clock ≤ post.clock + 17 ∧ post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → post.locals.lookup name = state.locals.lookup name) ∧
      (∀ output, result ≠ some (.returned output)) := by
  have aligned := evaluate_store_advance8_loop_local state keccakAbsorbAlignedStore.1 keccakAbsorbAlignedStore.2 initial name different ticks
  have unaligned := evaluate_store_advance8_loop_local state keccakAbsorbUnalignedStore.1 keccakAbsorbUnalignedStore.2 initial name different ticks
  rw [source_keccakAbsorb_loop_choice,evaluateHOLFiniteState_ite]
  split
  · split
    · obtain ⟨result,post,run,cost,remaining,noTimeout,completed,noReturn⟩ := unaligned
      exact ⟨result,post,run,cost,remaining,noTimeout,(fun normal => (completed normal).2.2),noReturn⟩
    · obtain ⟨result,post,run,cost,remaining,noTimeout,completed,noReturn⟩ := aligned
      exact ⟨result,post,run,cost,remaining,noTimeout,(fun normal => (completed normal).2.2),noReturn⟩
  · exact ⟨_,_,rfl,by omega,Nat.le_refl _,by simp,(by intro normal; cases normal),by intro output; simp⟩

#print axioms source_keccakAbsorb_loop_choice
#print axioms evaluate_keccakAbsorb_loop_choice_local
end InitECandidate.Runtime
