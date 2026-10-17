import InitECandidate.Runtime.HashDeleteLoopStepJournalSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The complete ranked deletion scan preserves the other live table. -/
theorem evaluate_hashDelete_loop_journal_supported {F : Type}
    (keyLength table keys stride capacity used values order orderPos items empty : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F)
    (valid : HashDeleteLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty bits state)
    (journal : BitVec 64) (count : Nat)
    (ready : JournalUndoRecords journal count state)
    (journalBound : journal.toNat + count * 32 ≤ 33806089496)
    (separated : orderPos.toNat + capacity.toNat * 8 ≤ journal.toNat ∨
      journal.toNat + count * 32 ≤ table.toNat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (budget : capacity.toNat * 55 ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state hashDeleteLoop = (none,post) ∧
      (HashDeleteLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty bits post ∧
       JournalUndoRecords journal count post) ∧
      state.clock ≤ post.clock + capacity.toNat * 55 ∧ post.clock ≤ state.clock := by
  let combined := fun current : PanSemStateFiniteExact 64 F =>
    HashDeleteLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty bits current ∧
    JournalUndoRecords journal count current
  have bounds := valid.rank_bounds keyLength table keys stride capacity used values order orderPos items empty bits state
  obtain ⟨post,run,postValid,cost,remaining⟩ := evaluate_hashDelete_loop_ranked_supported combined
    (hashDeleteStateRank capacity empty)
    (fun current currentValid => (currentValid.1.rank_bounds keyLength table keys stride capacity used values order orderPos items empty bits current).1)
    (fun current currentValid => ⟨currentValid.1.dec_clock keyLength table keys stride capacity used values order orderPos items empty bits current,
      currentValid.2.after_read current (decClockHOLFinite current) journal count rfl rfl⟩)
    (hashDeleteStateRank_dec_clock capacity empty)
    (fun current currentValid ticks => currentValid.1.step_supported_with_journal keyLength table keys stride capacity used values order orderPos items empty bits current
      journal count currentValid.2 journalBound separated supported ticks)
    state ⟨valid,ready⟩ (Nat.le_trans (Nat.mul_le_mul_right 55 bounds.2) budget)
  exact ⟨post,run,postValid,by have := Nat.mul_le_mul_right 55 bounds.2; omega,remaining⟩

#print axioms evaluate_hashDelete_loop_journal_supported
end InitECandidate.Runtime
