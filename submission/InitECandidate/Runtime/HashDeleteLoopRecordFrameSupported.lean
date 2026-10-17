import InitECandidate.Runtime.HashDeleteLoopStepRecordFrameSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The complete ranked deletion scan preserves the other live table. -/
theorem evaluate_hashDelete_loop_record_frame_supported {F : Type}
    (keyLength table keys stride capacity used values order orderPos items empty : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F)
    (valid : HashDeleteLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty bits state)
    (journal : BitVec 64) (count : Nat)
    (journalBound : journal.toNat + count * 32 ≤ 33806089496)
    (separated : orderPos.toNat + capacity.toNat * 8 ≤ journal.toNat ∨
      journal.toNat + count * 32 ≤ table.toNat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (budget : capacity.toNat * 55 ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state hashDeleteLoop = (none,post) ∧
      (HashDeleteLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty bits post ∧
       (∀ index : Nat, index < count → ∀ offset ∈ ([0,8,16,24] : List Nat),
        post.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) =
          state.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset))) ∧
      state.clock ≤ post.clock + capacity.toNat * 55 ∧ post.clock ≤ state.clock := by
  let combined := fun current : PanSemStateFiniteExact 64 F =>
    HashDeleteLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty bits current ∧
    (∀ index : Nat, index < count → ∀ offset ∈ ([0,8,16,24] : List Nat),
        current.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset) =
          state.memory (journal + BitVec.ofNat 64 index * 32 + BitVec.ofNat 64 offset))
  have bounds := valid.rank_bounds keyLength table keys stride capacity used values order orderPos items empty bits state
  obtain ⟨post,run,postValid,cost,remaining⟩ := evaluate_hashDelete_loop_ranked_supported combined
    (hashDeleteStateRank capacity empty)
    (fun current currentValid => (currentValid.1.rank_bounds keyLength table keys stride capacity used values order orderPos items empty bits current).1)
    (fun current currentValid => ⟨currentValid.1.dec_clock keyLength table keys stride capacity used values order orderPos items empty bits current,
      currentValid.2⟩)
    (hashDeleteStateRank_dec_clock capacity empty)
    (fun current currentValid ticks => by
      obtain ⟨post,⟨postValid,frame⟩,cost,remaining,body⟩ := currentValid.1.step_supported_with_record_frame
        keyLength table keys stride capacity used values order orderPos items empty bits current
        journal count journalBound separated supported ticks
      exact ⟨post,⟨postValid,by
        intro index inside offset member
        exact (frame index inside offset member).trans (currentValid.2 index inside offset member)⟩,cost,remaining,body⟩)
    state ⟨valid,by intro index inside offset member; rfl⟩ (Nat.le_trans (Nat.mul_le_mul_right 55 bounds.2) budget)
  exact ⟨post,run,postValid,by have := Nat.mul_le_mul_right 55 bounds.2; omega,remaining⟩

#print axioms evaluate_hashDelete_loop_record_frame_supported
end InitECandidate.Runtime
