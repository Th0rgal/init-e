import InitECandidate.Runtime.ValidateHeadersFirstSource
import InitECandidate.Runtime.WitnessArrayLinked
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def runAttemptAt (index : Nat) : ProgHOL 64 :=
  (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_run_attempt)

def runAttemptHeadersArguments : List (ExpHOL 64) :=
  [.load .one (.op .add [.var .local (ofString "si"),.const 72]),
   .load .one (.op .add [.var .local (ofString "si"),.const 80])]

theorem source_run_attempt_headers_call : runAttemptAt 2 =
    .decCall (ofString "vh") (.comb [.one,.one]) (ofString "validate_headers") runAttemptHeadersArguments (runAttemptAt 3) := rfl

/-- The actual run_attempt call reads the header array/count linked by the
original stateless decoder, including the record's memory-domain premises. -/
theorem eval_run_attempt_headers_arguments {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si headers count input length heap : BitVec 64)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word si)))
    (linked : WitnessArrayLinked s si 72 80 headers count input length heap) :
    evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) runAttemptHeadersArguments =
      some [.val (.word headers),.val (.word count)] := by
  have pointerDomain : s.memaddrs (si + (72#64)) := linked.pointerDomain
  have countDomain : s.memaddrs (si + (80#64)) := linked.countDomain
  have pointerCell : s.memory (si + (72#64)) = .word headers := linked.pointerCell
  have countCell : s.memory (si + (80#64)) = .word count := linked.countCell
  rw [evalListHOLFinite_eq_toExact]
  simp [runAttemptHeadersArguments,evalListHOLExact,evalHOLExact,atSi,wordOpHOL,wordOp,valueIsWord,valueWord,
    isWfShapeExactHOL,memLoadHOLExact,pointerDomain,countDomain,pointerCell,countCell]

#print axioms source_run_attempt_headers_call
#print axioms eval_run_attempt_headers_arguments
end InitECandidate.Runtime
