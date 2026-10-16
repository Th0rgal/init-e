import InitECandidate.Runtime.SourceClock
import InitECandidate.Runtime.BaselineGlobalEntry
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
set_option cbv.warning false
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Pancake.PanLang

/-- The actual generated global initializer contains no clock-consuming construct. -/
theorem baseline_globals_straightLine :
    straightLine (nestedSeqHOL FrontendStages.Declarations.globalInitializers) = true := by
  decide_cbv

/-- Its zero-clock property applies to every state, including failed initialization. -/
theorem baseline_globals_clock (state : PanSemStateFiniteExact 64 Guest.HostMemory) :
    (PanSemStateFiniteExact.evaluateHOLFiniteState state
      (nestedSeqHOL FrontendStages.Declarations.globalInitializers)).2.clock = state.clock :=
  clockPreserving_of_straightLine _ baseline_globals_straightLine state

/-- The concrete wrapper only needs the initializer run and the inner run;
clock preservation is certified from the actual initializer syntax. -/
theorem canonical_global_entry_clock (input : Guest.InputBlob)
    (initialized : PanSemStateFiniteExact 64 Guest.HostMemory)
    (initialRun : PanSemStateFiniteExact.evaluateHOLFiniteState
      {canonicalPanEntryState input with locals := HolFiniteMapExact.empty}
      (nestedSeqHOL FrontendStages.Declarations.globalInitializers) = (none,initialized))
    (fuel : Nat) (result : Option (PanSemResultExact 64))
    (post : PanSemStateFiniteExact 64 Guest.HostMemory)
    (run : PanSemStateFiniteExact.evaluateHOLFiniteState {initialized with clock := fuel}
      (.call none FrontendStages.Declarations.globalNewStart []) = (result,post)) :
    ∃ final, PanSemStateFiniteExact.evaluateHOLFiniteState
      {canonicalPanEntryState input with clock := fuel + 1}
      (.call none baselineCrepStart []) = (result,final) ∧ final.ffi = post.ffi := by
  have clock := baseline_globals_clock {canonicalPanEntryState input with locals := HolFiniteMapExact.empty}
  rw [initialRun] at clock
  exact canonical_global_entry_one_clock input initialized initialRun clock fuel result post run

#print axioms baseline_globals_straightLine
#print axioms baseline_globals_clock
#print axioms canonical_global_entry_clock
end InitECandidate.Runtime
