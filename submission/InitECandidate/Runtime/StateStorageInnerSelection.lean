import InitECandidate.Runtime.StateStorageValueTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def stateStorageInnerSelection : ProgHOL 64 :=
  .seq (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "m"))) (.const 0))
    (.seq (.call (some (some (.local,ofString "inner"),none)) (ofString "htab_new") [.const 32,.const 8])
      (.call (some (none,none)) (ofString "jset")
        [.var .local (ofString "outer"),.var .local (ofString "addr"),.var .local (ofString "inner")]))
    (.assign .local (ofString "inner") (.rfield 1 (.var .local (ofString "m"))))) stateStorageValueTail

def stateStorageInnerScope : ProgHOL 64 :=
  .dec (ofString "inner") .one (.const 0) stateStorageInnerSelection

theorem source_setStorage_inner_selection :
    stateInitSpineDrop 5 (sourceFunctionBody Guest.guestFn_set_storage) = stateStorageInnerSelection := by
  unfold sourceFunctionBody
  rw [declToHOL_eq]
  rfl

theorem source_setStorage_inner_scope :
    stateInitSpineDrop 4 (sourceFunctionBody Guest.guestFn_set_storage) = stateStorageInnerScope := by
  unfold sourceFunctionBody
  rw [declToHOL_eq]
  rfl

#print axioms source_setStorage_inner_selection
#print axioms source_setStorage_inner_scope
end InitECandidate.Runtime
