import InitECandidate.Runtime.RunAttemptHeaderCountReach
import InitECandidate.Runtime.HeaderPointerPrefix
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def runAttemptParentExpression : ExpHOL 64 :=
  .load .one (.op .add [.rfield 0 (.var .local (ofString "vh")),
    .panop .mul [.op .sub [.var .local (ofString "nh"),.const 1],.const 8]])

theorem source_run_attempt_parent : runAttemptAt 5 =
    .dec (ofString "parent") .one runAttemptParentExpression (runAttemptAt 6) := rfl

/-- The actual parent declaration selects the final header pointer from the
validated header-pointer buffer. Its content/domain premises are explicit:
they must be supplied by the header-loop buffer invariant. -/
theorem run_attempt_parent_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (headers hashes count parent : BitVec 64)
    (atHeaders : s.locals.lookup (ofString "vh") =
      some (.rStruct [.val (.word headers),.val (.word hashes)]))
    (atCount : s.locals.lookup (ofString "nh") = some (.val (.word count)))
    (domain : s.memaddrs (headers + (count - 1) * 8))
    (cell : s.memory (headers + (count - 1) * 8) = .word parent) :
    Reaches s (runAttemptAt 5)
      (fun ready => ready = setVarHOLFinite (ofString "parent") (.val (.word parent)) s)
      0 (runAttemptAt 6) := by
  have value : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) runAttemptParentExpression =
      some (.val (.word parent)) := by
    have dom : s.memaddrs (headers + (count - (1#64)) * (8#64)) := domain
    have word : s.memory (headers + (count - (1#64)) * (8#64)) = .word parent := cell
    simp [runAttemptParentExpression,evalHOLExact,evalListHOLExact,atHeaders,atCount,
      wordOpHOL,wordOp,panOpHOL,valueIsWord,valueWord,isWfShapeExactHOL,memLoadHOLExact,dom,word]
  rw [source_run_attempt_parent]
  apply reaches_dec
  intro v evaluated
  rw [value] at evaluated
  cases evaluated
  exact ⟨parent,rfl,rfl⟩

#print axioms source_run_attempt_parent
#print axioms run_attempt_parent_reaches

/-- The initialized buffer invariant discharges both memory premises of the
actual parent load, yielding an execution-derived typed parent pointer. -/
theorem run_attempt_parent_prefix_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (headers hashes count : BitVec 64)
    (atHeaders : s.locals.lookup (ofString "vh") =
      some (.rStruct [.val (.word headers),.val (.word hashes)]))
    (atCount : s.locals.lookup (ofString "nh") = some (.val (.word count)))
    (initialized : HeaderPointerPrefix s headers count.toNat) (nonzero : count ≠ 0) :
    ∃ parent : BitVec 64, Reaches s (runAttemptAt 5)
      (fun ready => ready = setVarHOLFinite (ofString "parent") (.val (.word parent)) s)
      0 (runAttemptAt 6) := by
  obtain ⟨domain,parent,word⟩ := initialized.last s headers count nonzero
  exact ⟨parent,run_attempt_parent_reaches s headers hashes count parent atHeaders atCount domain word⟩

#print axioms run_attempt_parent_prefix_reaches
end InitECandidate.Runtime
