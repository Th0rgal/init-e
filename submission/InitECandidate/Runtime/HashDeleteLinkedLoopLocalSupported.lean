import InitECandidate.Runtime.HashDeleteLinkedLoopSupported
import InitECandidate.Runtime.HashDeleteLoopLocalFrameSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete linked scan preserves any local outside its working set. -/
theorem evaluate_hashDelete_linked_loop_local_supported {F : Type}
    (keyLength table keys stride capacity used values order orderPos items empty deletedPosition : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F)
    (valid : HashDeleteLinkedLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty deletedPosition bits state)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (budget : capacity.toNat * 55 ≤ state.clock)
    (name : MlS) (notHole : name ≠ ofString "i") (notScan : name ≠ ofString "j")
    (notHash : name ≠ ofString "h") (notHome : name ≠ ofString "home") (notMovable : name ≠ ofString "movable") :
    ∃ post, evaluateHOLFiniteState state hashDeleteLoop = (none,post) ∧
      HashDeleteLinkedLoopExitWidth keyLength table keys stride capacity used values order orderPos items empty deletedPosition bits post ∧
      state.clock ≤ post.clock + capacity.toNat * 55 ∧ post.clock ≤ state.clock ∧
      post.locals.lookup name = state.locals.lookup name := by
  let inv := fun current : PanSemStateFiniteExact 64 F =>
    HashDeleteLinkedLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty deletedPosition bits current ∧
      current.locals.lookup name = state.locals.lookup name
  let finalCondition := fun current : PanSemStateFiniteExact 64 F =>
    HashDeleteLinkedLoopExitWidth keyLength table keys stride capacity used values order orderPos items empty deletedPosition bits current ∧
      current.locals.lookup name = state.locals.lookup name
  have bounds := valid.base.rank_bounds keyLength table keys stride capacity used values order orderPos items empty bits state
  obtain ⟨post,run,⟨exitValid,localSame⟩,cost,remaining⟩ := evaluate_hashDelete_loop_ranked_exit_supported inv finalCondition
    (hashDeleteStateRank capacity empty)
    (fun current currentValid => (currentValid.1.base.rank_bounds keyLength table keys stride capacity used values order orderPos items empty bits current).1)
    (fun current currentValid => ⟨currentValid.1.dec_clock keyLength table keys stride capacity used values order orderPos items empty deletedPosition bits current,currentValid.2⟩)
    (hashDeleteStateRank_dec_clock capacity empty)
    (by
      intro current currentValid ticks
      obtain ⟨next,cost,remaining,body⟩ := currentValid.1.step_supported keyLength table keys stride capacity used values order orderPos items empty deletedPosition bits current supported ticks
      have actual : ∃ result, evaluateHOLFiniteState current hashDeleteLoopBody = (result,next) := by
        rcases body with ⟨stopped,_⟩ | ⟨running,_,_⟩
        · exact ⟨_,stopped⟩
        · exact ⟨_,running⟩
      have frame := currentValid.1.base.body_local_frame_supported keyLength table keys stride capacity used values order orderPos items empty bits current next supported ticks actual name notHole notScan notHash notHome notMovable
      refine ⟨next,cost,remaining,?_⟩
      rcases body with ⟨stopped,exitValid⟩ | ⟨running,nextValid,decrease⟩
      · exact Or.inl ⟨stopped,exitValid,frame.trans currentValid.2⟩
      · exact Or.inr ⟨running,⟨nextValid,frame.trans currentValid.2⟩,decrease⟩)
    state ⟨valid,rfl⟩ (Nat.le_trans (Nat.mul_le_mul_right 55 bounds.2) budget)
  exact ⟨post,run,exitValid,by have := Nat.mul_le_mul_right 55 bounds.2; omega,remaining,localSame⟩

#print axioms evaluate_hashDelete_linked_loop_local_supported
end InitECandidate.Runtime
