import InitECandidate.Runtime.SourceTerminatesCanonicalEntry
import InitECandidate.Runtime.PanCompletedClockAgreement
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Completed runs with different starting clocks agree on their entire state
except the remaining clock, including the exact observable FFI event list. -/
theorem evaluate_completed_clock_state_agreement {F : Type} (state : PanSemStateFiniteExact 64 F)
    (program : ProgHOL 64) (firstClock secondClock : Nat)
    (firstResult secondResult : Option (PanSemResultExact 64))
    (firstPost secondPost : PanSemStateFiniteExact 64 F)
    (firstRun : evaluateHOLFiniteState {state with clock:=firstClock} program=(firstResult,firstPost))
    (secondRun : evaluateHOLFiniteState {state with clock:=secondClock} program=(secondResult,secondPost))
    (firstDone : firstResult≠some .timeOut) (secondDone : secondResult≠some .timeOut) :
    firstResult=secondResult ∧ {firstPost with clock:=0}={secondPost with clock:=0} := by
  have first := panPropsEvaluateAddClockEq program {state with clock:=firstClock} firstResult firstPost secondClock ⟨firstRun,firstDone⟩
  have second := panPropsEvaluateAddClockEq program {state with clock:=secondClock} secondResult secondPost firstClock ⟨secondRun,secondDone⟩
  change evaluateHOLFiniteState {state with clock:=firstClock+secondClock} program=_ at first
  change evaluateHOLFiniteState {state with clock:=secondClock+firstClock} program=_ at second
  rw [Nat.add_comm secondClock firstClock] at second
  have both := Prod.mk.inj (first.symm.trans second)
  exact ⟨both.1,congrArg (fun post=>{post with clock:=0}) both.2⟩

/-- A covered execution at the canonical installed entry is exactly a source
fuel witness for the unchanged challenge declarations. -/
theorem sourceTerminatesAt_of_canonical_entry (input : Guest.InputBlob)
    (outcome : HolOutcome) (events : List HolIoEvent) (fuel : Nat)
    (result : PanSemResultExact 64) (post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (run : evaluateHOLFiniteState {canonicalOriginalSourceEntry input with clock:=fuel}
      (.call none (ofString "main") [])=(some result,post))
    (terminal : match result with
      | .finalFfi ffi=>outcome=HolOutcome.ffiOutcome ffi
      | .returned _=>outcome=.success
      | _=>False)
    (trace : post.ffi.ioEvents=events) : sourceTerminatesAt input outcome events fuel := by
  classical
  refine ⟨[],canonicalOriginalSourceEntry input,result,post,?_,?_,run,?_,trace⟩
  · exact original_declaration_context.symm.trans sourceStructContext
  · exact (original_declaration_evaluation (sourceInitialState input)).symm.trans
      (canonical_original_declarations_evaluate input)
  · cases result <;> exact terminal

/-- Any non-timeout canonical run supplies a bounded fuel witness for an input
already known to have the covered source observation. Exact events are retained. -/
theorem sourceTerminatesAt_of_canonical_non_timeout (input : Guest.InputBlob)
    (outcome : HolOutcome) (events : List HolIoEvent) (oldFuel fuel : Nat)
    (source : sourceTerminatesAt input outcome events oldFuel)
    (safe : (evaluateHOLFiniteState {canonicalOriginalSourceEntry input with clock:=fuel}
      (.call none (ofString "main") [])).1≠some .timeOut) :
    sourceTerminatesAt input outcome events fuel := by
  obtain ⟨result,post,run,terminal,trace⟩ := sourceTerminatesAt_canonical_entry input outcome events oldFuel source
  have completed : some result≠some (.timeOut : PanSemResultExact 64) := by
    intro bad
    have same := Option.some.inj bad
    rw [same] at terminal
    exact terminal
  cases newRun : evaluateHOLFiniteState {canonicalOriginalSourceEntry input with clock:=fuel}
      (.call none (ofString "main") []) with
  | mk nextResult nextPost =>
    have safeNext : nextResult≠some .timeOut := by simpa only [newRun] using safe
    obtain ⟨sameResult,sameState⟩ := evaluate_completed_clock_state_agreement (canonicalOriginalSourceEntry input)
      (.call none (ofString "main") []) oldFuel fuel (some result) nextResult post nextPost run newRun completed safeNext
    subst nextResult
    have sameTrace := congrArg (fun state=>state.ffi.ioEvents) sameState
    exact sourceTerminatesAt_of_canonical_entry input outcome events fuel result nextPost newRun (by cases result <;> exact terminal)
      (sameTrace.symm.trans trace)

/-- Closing a quantitative source certificate only requires the actual
canonical main call to avoid timeout at the proposed finite budget. -/
theorem sourceBound_of_canonical_non_timeout (bound : Guest.InputBlob→Nat)
    (safe : ∀ input, Guest.GasLimit.declaredGasLimit input≤200000000 →
      (evaluateHOLFiniteState {canonicalOriginalSourceEntry input with clock:=bound input}
        (.call none (ofString "main") [])).1≠some .timeOut) : SourceBound bound := by
  intro input gas outcome events behavior covered
  obtain ⟨oldFuel,source⟩ := sourceTerminatesAt_exists input outcome events behavior
  exact ⟨bound input,Nat.le_refl _,sourceTerminatesAt_of_canonical_non_timeout input outcome events oldFuel
    (bound input) source (safe input gas)⟩

#print axioms evaluate_completed_clock_state_agreement
#print axioms sourceTerminatesAt_of_canonical_entry
#print axioms sourceTerminatesAt_of_canonical_non_timeout
#print axioms sourceBound_of_canonical_non_timeout
end InitECandidate.Runtime
