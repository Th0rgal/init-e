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

/-- A raise either produces its declared exception or a shape error; both
are terminal, timeout-free outcomes with no source clock consumption. -/
theorem raise_constant_stAbort {F : Type} (s : PanSemStateFiniteExact 64 F)
    (name : MlS) (value : BitVec 64) :
    StAbort s (evaluateHOLFiniteState s (.raise name (.const value))) 0 := by
  simp only [evaluateHOLFiniteState_raise,evalHOLExact]
  split
  · split
    · exact ⟨_,rfl,by intro v; simp,by simp [emptyLocalsHOLFinite],by simp [emptyLocalsHOLFinite],by simp⟩
    · exact stAbort_error s 0
  · exact stAbort_error s 0

/-- The actual empty-header guard either passes with a nonzero count or
terminates in the exception/error branch, without clock consumption. -/
theorem run_attempt_header_guard_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (count : BitVec 64)
    (atCount : s.locals.lookup (ofString "nh") = some (.val (.word count))) :
    Reaches s (runAttemptAt 4) (fun ready => ready = s ∧ count ≠ 0) 0 (runAttemptAt 5) := by
  by_cases zero : count = 0
  · subst count
    right
    rw [source_run_attempt_header_count_guard]
    apply stAbort_seq
    have reduced : evaluateHOLFiniteState s runAttemptHeaderCountGuard =
        evaluateHOLFiniteState s (.raise (ofString "BlockErr") (.const 3)) := by
      rw [runAttemptHeaderCountGuard,evaluateHOLFiniteState_ite]
      simp [evalHOLExact,atCount,Compiler.Encoders.Asm.wordCmpHOL]
    rw [reduced]
    exact raise_constant_stAbort s _ _
  · exact reaches_mono s _ _ _ _ 0 0 (le_refl _) (fun ready same => ⟨same,zero⟩)
      (run_attempt_nonempty_header_guard_reaches s count atCount zero)

#print axioms raise_constant_stAbort
#print axioms run_attempt_header_guard_reaches

/-- The actual reload and guard compose into a zero-tick prefix, with an
execution-derived nonempty count on the branch reaching the parent load. -/
theorem run_attempt_header_count_and_guard_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si count : BitVec 64)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word si)))
    (domain : s.memaddrs (si + (80#64)))
    (cell : s.memory (si + (80#64)) = .word count) :
    Reaches s (runAttemptAt 3)
      (fun ready => ready = setVarHOLFinite (ofString "nh") (.val (.word count)) s ∧ count ≠ 0)
      0 (runAttemptAt 5) := by
  have reached := run_attempt_header_count_reaches s si count atSi domain cell
  have composed := reaches_trans s (runAttemptAt 3) (runAttemptAt 4) (runAttemptAt 5)
    _ _ 0 0 reached (fun next same => by
      subst next
      exact run_attempt_header_guard_reaches _ count (by simp [setVarHOLFinite,FUPDATE]))
  exact composed

#print axioms run_attempt_header_count_and_guard_reaches
end InitECandidate.Runtime
