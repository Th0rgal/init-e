import InitECandidate.Runtime.RunAttemptHeadersSource
import InitECandidate.Runtime.WitnessArrayLinked
import InitECandidate.Runtime.OriginalNodedbBuildCode
import InitECandidate.Runtime.PanTwoWordResultLookup
/-!
The actual `nodedb`/`codedb` argument loads of `run_attempt`.

The real runtime calls `nodedb_build` twice: at `runAttemptAt 9` with the two
loaded words at `si + 40` and `si + 48`, and at `runAttemptAt 10` with the two
loaded words at `si + 56` and `si + 64`.  Both reads are the same
`WitnessArrayLinked` record shape used by the header call (a typed pointer cell,
a typed count cell, and the record's memory-domain premises), so the argument
lists evaluate to the two loaded words and the original code lookup returns the
actual single-word `nodedb_build` body with its bound parameter locals.

Nothing about runtime bounds is stated here: this module only supplies the
source shapes and the argument/code facts.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 400000

/-- The actual `nodedb` argument list read by `run_attempt`. -/
def runAttemptNodedbArguments : List (ExpHOL 64) :=
  [.load .one (.op .add [.var .local (ofString "si"),.const 40]),
   .load .one (.op .add [.var .local (ofString "si"),.const 48])]

/-- The actual `codedb` argument list read by `run_attempt`. -/
def runAttemptCodedbArguments : List (ExpHOL 64) :=
  [.load .one (.op .add [.var .local (ofString "si"),.const 56]),
   .load .one (.op .add [.var .local (ofString "si"),.const 64])]

/-- The bound parameter locals of one actual `nodedb_build` call. -/
def nodedbBuildCallee (pointer count : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  (HolFiniteMapExact.empty.update (ofString "slice_arr",.val (.word pointer))).update
    (ofString "n",.val (.word count))

/-- The actual source at `runAttemptAt 9` is the real `nodedb` call. -/
theorem source_run_attempt_nodedb_call : runAttemptAt 9 =
    .decCall (ofString "nodedb") .one (ofString "nodedb_build")
      runAttemptNodedbArguments (runAttemptAt 10) := rfl

/-- The actual source at `runAttemptAt 10` is the real `codedb` call. -/
theorem source_run_attempt_codedb_call : runAttemptAt 10 =
    .decCall (ofString "codedb") .one (ofString "nodedb_build")
      runAttemptCodedbArguments (runAttemptAt 11) := rfl

/-- The actual `nodedb` argument loads read the record's typed pointer and count
cells at `si + 40` and `si + 48`. -/
theorem eval_run_attempt_nodedb_arguments {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si pointer count input length heap : BitVec 64)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word si)))
    (linked : WitnessArrayLinked s si 40 48 pointer count input length heap) :
    evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      runAttemptNodedbArguments = some [.val (.word pointer),.val (.word count)] := by
  have pointerDomain : s.memaddrs (si + (40#64)) := linked.pointerDomain
  have countDomain : s.memaddrs (si + (48#64)) := linked.countDomain
  have pointerCell : s.memory (si + (40#64)) = .word pointer := linked.pointerCell
  have countCell : s.memory (si + (48#64)) = .word count := linked.countCell
  rw [evalListHOLFinite_eq_toExact]
  simp [runAttemptNodedbArguments,evalListHOLExact,evalHOLExact,atSi,wordOpHOL,wordOp,valueIsWord,valueWord,
    isWfShapeExactHOL,memLoadHOLExact,pointerDomain,countDomain,pointerCell,countCell]

/-- The actual `codedb` argument loads read the record's typed pointer and count
cells at `si + 56` and `si + 64`. -/
theorem eval_run_attempt_codedb_arguments {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si pointer count input length heap : BitVec 64)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word si)))
    (linked : WitnessArrayLinked s si 56 64 pointer count input length heap) :
    evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      runAttemptCodedbArguments = some [.val (.word pointer),.val (.word count)] := by
  have pointerDomain : s.memaddrs (si + (56#64)) := linked.pointerDomain
  have countDomain : s.memaddrs (si + (64#64)) := linked.countDomain
  have pointerCell : s.memory (si + (56#64)) = .word pointer := linked.pointerCell
  have countCell : s.memory (si + (64#64)) = .word count := linked.countCell
  rw [evalListHOLFinite_eq_toExact]
  simp [runAttemptCodedbArguments,evalListHOLExact,evalHOLExact,atSi,wordOpHOL,wordOp,valueIsWord,valueWord,
    isWfShapeExactHOL,memLoadHOLExact,pointerDomain,countDomain,pointerCell,countCell]

/-- Original code lookup supplies the actual single-word `nodedb_build` body and
its bound parameter locals for the two loaded words. -/
theorem lookup_nodedb_build_callee (pointer count : BitVec 64) :
    lookupCodeHOLFinite originalRuntimeCode.lookup (ofString "nodedb_build")
      [.val (.word pointer),.val (.word count)] =
      some (sourceFunctionBody Guest.guestFn_nodedb_build,nodedbBuildCallee pointer count,.one) :=
  pan_two_word_result_lookup _ _ _ _ _ pointer count .one (by decide)
    originalRuntimeCode_nodedbBuild_lookup

#print axioms source_run_attempt_nodedb_call
#print axioms source_run_attempt_codedb_call
#print axioms eval_run_attempt_nodedb_arguments
#print axioms eval_run_attempt_codedb_arguments
#print axioms lookup_nodedb_build_callee
end InitECandidate.Runtime
