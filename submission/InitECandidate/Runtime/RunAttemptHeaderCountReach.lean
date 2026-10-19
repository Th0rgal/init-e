import InitECandidate.Runtime.RunAttemptHeadersSource
import InitECandidate.Runtime.StatelessReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def runAttemptHeaderCountExpression : ExpHOL 64 :=
  .load .one (.op .add [.var .local (ofString "si"),.const 80])

theorem source_run_attempt_header_count : runAttemptAt 3 =
    .dec (ofString "nh") .one runAttemptHeaderCountExpression (runAttemptAt 4) := rfl

/-- The count reload after validation uses the retained stateless-input
record cell. It introduces no source clock tick and preserves the complete
state except for the new local. -/
theorem run_attempt_header_count_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si count : BitVec 64)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word si)))
    (domain : s.memaddrs (si + (80#64)))
    (cell : s.memory (si + (80#64)) = .word count) :
    Reaches s (runAttemptAt 3)
      (fun ready => ready = setVarHOLFinite (ofString "nh") (.val (.word count)) s)
      0 (runAttemptAt 4) := by
  have value : @evalHOLExact 64 F _ s.toExact
      (fun a => Classical.propDecidable (s.memaddrs a)) runAttemptHeaderCountExpression =
      some (.val (.word count)) := by
    simp [runAttemptHeaderCountExpression,evalHOLExact,evalListHOLExact,atSi,wordOpHOL,wordOp,valueIsWord,valueWord,
      isWfShapeExactHOL,memLoadHOLExact,domain,cell]
  rw [source_run_attempt_header_count]
  apply reaches_dec
  intro v evaluated
  rw [value] at evaluated
  cases evaluated
  exact ⟨count,rfl,rfl⟩

#print axioms source_run_attempt_header_count
#print axioms run_attempt_header_count_reaches

def runAttemptHeaderCountGuard : ProgHOL 64 :=
  .ite (.cmp .equal (.var .local (ofString "nh")) (.const 0))
    (.raise (ofString "BlockErr") (.const 3)) .skip

theorem source_run_attempt_header_count_guard : runAttemptAt 4 =
    .seq runAttemptHeaderCountGuard (runAttemptAt 5) := rfl

/-- A successful nonempty-header check reaches the parent-header load
without consuming a source clock tick. -/
theorem run_attempt_nonempty_header_guard_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (count : BitVec 64)
    (atCount : s.locals.lookup (ofString "nh") = some (.val (.word count)))
    (nonzero : count ≠ 0) :
    Reaches s (runAttemptAt 4) (fun ready => ready = s) 0 (runAttemptAt 5) := by
  rw [source_run_attempt_header_count_guard]
  apply reaches_seq
  left
  refine ⟨s,rfl,by omega,le_refl _,?_⟩
  rw [runAttemptHeaderCountGuard,evaluateHOLFiniteState_ite]
  have nz : count ≠ (0#64) := nonzero
  simp [evalHOLExact,atCount,Compiler.Encoders.Asm.wordCmpHOL,nz,evaluateHOLFiniteState_skip]

#print axioms source_run_attempt_header_count_guard
#print axioms run_attempt_nonempty_header_guard_reaches
end InitECandidate.Runtime
