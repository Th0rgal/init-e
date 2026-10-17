import InitECandidate.Runtime.StateRestoreRecordLoads
import InitECandidate.Runtime.StateRestoreRank
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem evaluate_stateRestore_record_loads {F : Type} (state : PanSemStateFiniteExact 64 F)
    (record table key : BitVec 64)
    (r : state.locals.lookup (ofString "r") = some (.val (.word record)))
    (tableDomain : state.memaddrs record) (tableCell : state.memory record = .word table)
    (keyDomain : state.memaddrs (record + 8)) (keyCell : state.memory (record + 8) = .word key) :
    evaluateHOLFiniteState state
      (.dec (ofString "t") .one (.load .one (.var .local (ofString "r")))
        (.dec (ofString "key") .one (.load .one (hashLocalAddress (ofString "r") 8)) stateRestoreRecordDecision)) =
      (let output := evaluateHOLFiniteState
          (setVarHOLFinite (ofString "key") (.val (.word key)) (setVarHOLFinite (ofString "t") (.val (.word table)) state)) stateRestoreRecordDecision;
        (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq
          (HolFiniteMapExact.resVarEq output.2.locals (ofString "key",state.locals.lookup (ofString "key")))
          (ofString "t",state.locals.lookup (ofString "t")))})) := by
  have loaded : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.load .one (.var .local (ofString "r"))) = some (.val (.word table)) := by
    simp [evalHOLExact,r,isWfShapeExactHOL,memLoadHOLExact,tableDomain,tableCell]
  let tableState := setVarHOLFinite (ofString "t") (.val (.word table)) state
  have rAfter : tableState.locals.lookup (ofString "r") = some (.val (.word record)) := by
    have distinct : ofString "t" ≠ ofString "r" := by decide
    simpa [tableState,setVarHOLFinite,FUPDATE,distinct] using r
  have scope := evaluate_header_load_scope tableState (ofString "key") (ofString "r") record 8 key
    stateRestoreRecordDecision rAfter keyDomain keyCell
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [loaded]
  simp only [shapeOfHOLExact,shapeEqHOL,ite_true]
  rw [scope]
  rfl

/-- Restoring a temporary local other than snap cannot alter the rollback rank. -/
theorem stateRestoreRank_restore_local {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (saved : Option (ValueHOL 64)) (different : name ≠ ofString "snap") :
    stateRestoreRank {state with locals := HolFiniteMapExact.resVarEq state.locals (name,saved)} = stateRestoreRank state := by
  have lookup : (HolFiniteMapExact.resVarEq state.locals (name,saved)).lookup (ofString "snap") = state.locals.lookup (ofString "snap") := by
    cases saved <;> simp [HolFiniteMapExact.lookup_resVarEq_none,HolFiniteMapExact.lookup_resVarEq_some,FDOMSUB_HOL,FUPDATE_HOL,different,Ne.symm different]
  simp only [stateRestoreRank,lookup]

#print axioms evaluate_stateRestore_record_loads
#print axioms stateRestoreRank_restore_local
end InitECandidate.Runtime
