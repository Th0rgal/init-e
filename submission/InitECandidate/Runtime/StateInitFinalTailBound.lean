import InitECandidate.Runtime.StateInitJournalSource
import InitECandidate.Runtime.ProgBounded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
/-- Exact original initializer suffix after all table constructors. -/
theorem source_state_init_final_tail : stateInitSpineDrop 26 (sourceFunctionBody Guest.guestFn_state_init) =
 .seq (.call (some (some (.global,ofString "sk_buf"),none)) (ofString "alloc") [.const 64]) stateInitJournalTail := by
 unfold stateInitJournalTail sourceFunctionBody
 rw [InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
 rfl
/-- Journal fixed-capacity allocation/reset includes allocator rejection and every access failure. -/
theorem state_init_journal_tail_bounded : ProgBounded stateInitJournalTail 2 := by
 unfold stateInitJournalTail
 intro F state code budget
 exact ProgBounded.seq (a:=0) (b:=2) (ProgBounded.straight _ rfl)
  (ProgBounded.seq (a:=2) (b:=0) (ProgBounded.alloc _ _)
   (ProgBounded.straight _ rfl)) state code budget
/-- Actual final scratch/journal allocations take at most four source ticks, without room assumptions. -/
theorem state_init_final_tail_bounded : ProgBounded
 (stateInitSpineDrop 26 (sourceFunctionBody Guest.guestFn_state_init)) 4 := by
 rw [source_state_init_final_tail]
 intro F state code budget
 exact ProgBounded.seq (ProgBounded.alloc _ _) state_init_journal_tail_bounded state code budget
#print axioms source_state_init_final_tail
#print axioms state_init_journal_tail_bounded
#print axioms state_init_final_tail_bounded
end InitECandidate.Runtime
