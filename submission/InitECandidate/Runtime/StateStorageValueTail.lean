import InitECandidate.Runtime.StateInitJournalSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def stateStorageValueTail : ProgHOL 64 :=
  .decCall (ofString "v") .one (ofString "alloc") [.const 32]
    (.seq (.store (.var .local (ofString "v")) (.var .local (ofString "value")))
      (.seq (.call (some (none,none)) (ofString "jset")
        [.var .local (ofString "inner"),.var .local (ofString "key"),.var .local (ofString "v")]) (.return (.const 0))))

/-- The value-allocation/journal-update tail is exactly the original source
continuation after the existing/new-inner-table selection. -/
theorem source_setStorage_value_tail :
    stateInitSpineDrop 6 (sourceFunctionBody Guest.guestFn_set_storage) = stateStorageValueTail := by
  unfold sourceFunctionBody
  rw [declToHOL_eq]
  rfl

#print axioms source_setStorage_value_tail
end InitECandidate.Runtime
