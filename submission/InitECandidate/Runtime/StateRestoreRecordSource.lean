import InitECandidate.Runtime.StateRestoreLoop
import InitECandidate.Runtime.HashInsertCountTail
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
open InitECandidate.Proofs.FrontendCodecComputation

def stateRestoreRecordDecision : ProgHOL 64 :=
  .ite (.cmp .notEqual (.load .one (hashLocalAddress (ofString "r") 16)) (.const 0))
    (.call (some (none,none)) (ofString "htab_set")
      [.var .local (ofString "t"),.var .local (ofString "key"),.load .one (hashLocalAddress (ofString "r") 24)])
    (.call (some (none,none)) (ofString "htab_del")
      [.var .local (ofString "t"),.var .local (ofString "key")])

theorem stateRestore_apply_record_shape : stateRestoreApplyRecord =
    .dec (ofString "r") .one (.op .add [.var .global (ofString "journal"),
      .panop .mul [.var .global (ofString "journal_n"),.const 32]])
      (.dec (ofString "t") .one (.load .one (.var .local (ofString "r")))
        (.dec (ofString "key") .one (.load .one (hashLocalAddress (ofString "r") 8))
          stateRestoreRecordDecision)) := by
  simp only [stateRestoreApplyRecord,stateRestoreLoopBody,stateRestoreDecodedBody,stateRestoreRecordDecision,
    hashLocalAddress,Guest.guestFn_state_restore,declToHOLStructural,funDeclToHOLStructural,progToHOLStructural,
    expToHOLStructural,expListToHOLStructural,shapeToHOLStructural,List.map_cons,List.map_nil,Option.map_none]
  rfl

#print axioms stateRestore_apply_record_shape
end InitECandidate.Runtime
