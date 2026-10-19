import InitECandidate.Runtime.RunAttemptHeadersSource
import InitECandidate.Runtime.StatelessReach
/-!
The actual `run_attempt` source prefix: the original body starts with the local
declaration `pl = load(si + 0)` followed by a `skip`, and those two instructions
reach the real header-validation call site within zero clock ticks.

This is the entry bridge between the actual caller (`si` typed, its first record
word `si + 0` readable and holding `payload`) and the checked declaration
composition starting at `runAttemptAt 2`.  It assumes nothing about later code.
-/
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 800000

/-- The original `run_attempt` body is the structural function body. -/
theorem source_run_attempt_body :
    runAttemptAt 0 = sourceFunctionBody Guest.guestFn_run_attempt := by
  rw [sourceFunctionBody_eq_structural]
  rfl

/-- Shape of the original `run_attempt` prefix: the `pl` declaration loads the
first record word, then a `skip` precedes the header-validation call. -/
theorem source_run_attempt_prefix :
    runAttemptAt 0 = .dec (ofString "pl") .one
      (.load .one (.op .add [.var .local (ofString "si"),.const 0])) (runAttemptAt 1) ∧
    runAttemptAt 1 = .seq .skip (runAttemptAt 2) := by
  exact ⟨rfl,rfl⟩

/-- The actual `run_attempt` prefix reaches the header-validation call site in
zero ticks: the source `s.locals` gains exactly `pl = payload`, and memory,
globals, domain and code are untouched. -/
theorem run_attempt_initial_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (si payload : BitVec 64)
    (atSi : s.locals.lookup (ofString "si") = some (.val (.word si)))
    (siDomain : s.memaddrs (si + (0#64)))
    (siCell : s.memory (si + (0#64)) = .word payload) :
    Reaches s (runAttemptAt 0)
      (fun ready => ready.locals = s.locals.update (ofString "pl",.val (.word payload)) ∧
        ready.locals.lookup (ofString "pl") = some (.val (.word payload)) ∧
        ready.memory = s.memory ∧ ready.globals = s.globals ∧
        ready.memaddrs = s.memaddrs ∧ ready.code = s.code)
      0 (runAttemptAt 2) := by
  obtain ⟨bodyShape,skipShape⟩ := source_run_attempt_prefix
  rw [bodyShape]
  refine reaches_trans s (.dec (ofString "pl") .one
      (.load .one (.op .add [.var .local (ofString "si"),.const 0])) (runAttemptAt 1))
    (runAttemptAt 1) (runAttemptAt 2)
    (fun E => E = setVarHOLFinite (ofString "pl") (.val (.word payload)) s)
    (fun ready => ready.locals = s.locals.update (ofString "pl",.val (.word payload)) ∧
      ready.locals.lookup (ofString "pl") = some (.val (.word payload)) ∧
      ready.memory = s.memory ∧ ready.globals = s.globals ∧
      ready.memaddrs = s.memaddrs ∧ ready.code = s.code) 0 0 ?_ ?_
  · apply reaches_dec
    intro v loaded
    have domainSi : s.memaddrs si := by simpa using siDomain
    have cellSi : s.memory si = .word payload := by simpa using siCell
    have valueEq : v = .val (.word payload) := by
      simp [evalHOLExact,evalListHOLExact,atSi,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,
        memLoadHOLExact,List.map_cons,List.map_nil,domainSi,cellSi] at loaded
      simpa using loaded.symm
    subst valueEq
    exact ⟨payload,rfl,rfl⟩
  · intro next nextEq
    subst nextEq
    rw [skipShape]
    apply reaches_seq
    refine Or.inl ⟨setVarHOLFinite (ofString "pl") (.val (.word payload)) s,
      ⟨rfl,?_,rfl,rfl,rfl,rfl⟩,?_,le_refl _,?_⟩
    · simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    · simp
    exact evaluateHOLFiniteState_skip _

#print axioms source_run_attempt_body
#print axioms source_run_attempt_prefix
#print axioms run_attempt_initial_reaches
end InitECandidate.Runtime
