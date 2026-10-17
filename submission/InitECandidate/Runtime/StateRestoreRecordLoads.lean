import InitECandidate.Runtime.StateRestoreRecordDecisionBound
import InitECandidate.Runtime.HeaderLoadScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Loading the journal record fields and restoring their local scopes consumes
no additional source clock ticks. -/
theorem stateRestore_record_loads_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (record table key : BitVec 64) (bound : Nat)
    (r : state.locals.lookup (ofString "r") = some (.val (.word record)))
    (tableDomain : state.memaddrs record) (tableCell : state.memory record = .word table)
    (keyDomain : state.memaddrs (record + 8)) (keyCell : state.memory (record + 8) = .word key)
    (bounded : let entry := setVarHOLFinite (ofString "key") (.val (.word key)) (setVarHOLFinite (ofString "t") (.val (.word table)) state);
      entry.clock ≤ (evaluateHOLFiniteState entry stateRestoreRecordDecision).2.clock + bound ∧
        (evaluateHOLFiniteState entry stateRestoreRecordDecision).2.clock ≤ entry.clock) :
    let body : ProgHOL 64 := .dec (ofString "t") .one (.load .one (.var .local (ofString "r")))
      (.dec (ofString "key") .one (.load .one (hashLocalAddress (ofString "r") 8)) stateRestoreRecordDecision)
    state.clock ≤ (evaluateHOLFiniteState state body).2.clock + bound ∧
      (evaluateHOLFiniteState state body).2.clock ≤ state.clock := by
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
  dsimp only
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  rw [loaded]
  simp only [shapeOfHOLExact,shapeEqHOL,ite_true]
  rw [scope]
  exact bounded

#print axioms stateRestore_record_loads_bounded
end InitECandidate.Runtime
