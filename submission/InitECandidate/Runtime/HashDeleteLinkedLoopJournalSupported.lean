import InitECandidate.Runtime.HashDeleteLinkedLoopMetadataSupported
import InitECandidate.Runtime.HashDeleteLoopJournalSupported
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact

/-- Linked final-hole information and another table survive the same actual scan. -/
theorem evaluate_hashDelete_linked_loop_journal_supported {F : Type}
    (keyLength table keys stride capacity used values order orderPos items empty deletedPosition : BitVec 64) (bits : Nat)
    (state : PanSemStateFiniteExact 64 F)
    (valid : HashDeleteLinkedLoopInvariantWidth keyLength table keys stride capacity used values order orderPos items empty deletedPosition bits state)
    (journal : BitVec 64) (count : Nat)
    (ready : JournalUndoRecords journal count state)
    (journalBound : journal.toNat + count * 32 ≤ 33806089496)
    (separated : orderPos.toNat + capacity.toNat * 8 ≤ journal.toNat ∨
      journal.toNat + count * 32 ≤ table.toNat)
    (supported : keyLength = 20 ∨ keyLength = 32 ∨ keyLength = 52)
    (budget : capacity.toNat * 55 ≤ state.clock) :
    ∃ post, evaluateHOLFiniteState state hashDeleteLoop = (none,post) ∧
      HashDeleteLinkedLoopExitWidth keyLength table keys stride capacity used values order orderPos items empty deletedPosition bits post ∧
      JournalUndoRecords journal count post ∧
      state.clock ≤ post.clock + capacity.toNat * 55 ∧ post.clock ≤ state.clock ∧
      post.globals = state.globals ∧ post.code = state.code ∧ post.memaddrs = state.memaddrs ∧ post.be = state.be := by
  obtain ⟨post,run,exitValid,cost,remaining,globals,code,domain,endian⟩ := evaluate_hashDelete_linked_loop_metadata_supported
    keyLength table keys stride capacity used values order orderPos items empty deletedPosition bits state valid supported budget
  obtain ⟨checked,checkedRun,⟨_,preserved⟩,_,_⟩ := evaluate_hashDelete_loop_journal_supported
    keyLength table keys stride capacity used values order orderPos items empty bits state valid.base
    journal count ready journalBound separated supported budget
  have same : post = checked := congrArg Prod.snd (run.symm.trans checkedRun)
  exact ⟨post,run,exitValid,by rw [same]; exact preserved,cost,remaining,globals,code,domain,endian⟩

#print axioms evaluate_hashDelete_linked_loop_journal_supported
end InitECandidate.Runtime
