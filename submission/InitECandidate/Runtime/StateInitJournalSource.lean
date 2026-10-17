import InitECandidate.Runtime.StateFreshTxSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

/-- Follow the actual initializer's sequential and declaration continuation spine. -/
def stateInitSpineDrop : Nat → ProgHOL 64 → ProgHOL 64
  | 0, program => program
  | n + 1, .seq _ rest => stateInitSpineDrop n rest
  | n + 1, .decCall _ _ _ _ rest => stateInitSpineDrop n rest
  | n + 1, .dec _ _ _ rest => stateInitSpineDrop n rest
  | _, program => program

def stateInitJournalTail : ProgHOL 64 :=
  .seq (.assign .global (ofString "journal_cap") (.const 524288))
    (.seq (.call (some (some (.global,ofString "journal"),none)) (ofString "alloc")
      [.panop .mul [.var .global (ofString "journal_cap"),.const 32]])
      (.seq (.assign .global (ofString "journal_n") (.const 0))
        (.seq (.assign .global (ofString "ts") (.const 0)) (.return (.const 0)))))

/-- The journal allocation/reset block is the exact suffix of the frozen
initializer after scratch allocation, inside its original declaration scopes. -/
theorem source_stateInit_journal_tail :
    stateInitSpineDrop 27 (sourceFunctionBody Guest.guestFn_state_init) = stateInitJournalTail := by
  unfold sourceFunctionBody
  rw [declToHOL_eq]
  rfl

#print axioms source_stateInit_journal_tail
end InitECandidate.Runtime
