import InitECandidate.Runtime.RunAttemptHeadersSource
import Flapjack.Pancake.Semantics.PanSem.EvaluateClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- The actual initializer reads the parent header state-root pointer. -/
def runAttemptStateInitArguments : List (ExpHOL 64) :=
  [.var .local (ofString "nodedb"),
   .load .one (.op .add [.var .local (ofString "parent"),.const 32]),
   .var .local (ofString "codedb")]

theorem source_run_attempt_state_init_call : runAttemptAt 11 =
    .seq (.call (some (none,none)) (ofString "state_init") runAttemptStateInitArguments)
      (runAttemptAt 12) := rfl

/-- Actual initializer arguments, with the parent cell read from caller memory.
This makes no assumption about an initializer bound or its returned state. -/
theorem eval_run_attempt_state_init_arguments {F : Type} (s : PanSemStateFiniteExact 64 F)
    (nodeTable parent stateRoot codeTable : BitVec 64)
    (nodes : s.locals.lookup (ofString "nodedb") = some (.val (.word nodeTable)))
    (atParent : s.locals.lookup (ofString "parent") = some (.val (.word parent)))
    (codes : s.locals.lookup (ofString "codedb") = some (.val (.word codeTable)))
    (domain : s.memaddrs (parent + (32#64)))
    (cell : s.memory (parent + (32#64)) = .word stateRoot) :
    evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      runAttemptStateInitArguments =
        some [.val (.word nodeTable),.val (.word stateRoot),.val (.word codeTable)] := by
  rw [evalListHOLFinite_eq_toExact]
  simp [runAttemptStateInitArguments,evalListHOLExact,evalHOLExact,nodes,atParent,codes,
    wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,domain,cell]

#print axioms source_run_attempt_state_init_call
#print axioms eval_run_attempt_state_init_arguments
end InitECandidate.Runtime
