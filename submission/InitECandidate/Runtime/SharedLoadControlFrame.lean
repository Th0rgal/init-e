import InitECandidate.Runtime.SourceClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A local shared-memory load costs no source ticks. On normal completion
it installs a word and preserves every other local; terminal host events
and invalid accesses are explicit alternatives. -/
theorem evaluate_shared_load_control_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (operator : OpSize) (name : MlS) (address : ExpHOL 64) :
    let evaluated := evaluateHOLFiniteState state (.shMemLoad operator .local name address)
    evaluated.2.clock = state.clock ∧
      (evaluated.1 = none ∨ evaluated.1 = some .error ∨ ∃ event, evaluated.1 = some (.finalFfi event)) ∧
      evaluated.2.globals = state.globals ∧ evaluated.2.memory = state.memory ∧ evaluated.2.memaddrs = state.memaddrs ∧
      (evaluated.1 = none → ∃ word : BitVec 64,
        evaluated.2.locals.lookup name = some (.val (.word word)) ∧
        ∀ key, key ≠ name → evaluated.2.locals.lookup key = state.locals.lookup key) := by
  classical
  rw [evaluateHOLFiniteState_shMemLoad_source]
  dsimp only
  split
  · split
    · unfold shMemLoadHOLFiniteExact
      split <;> split
      all_goals simp [setKvarFfiHOLFinite,setKvarHOLFinite,setVarHOLFinite,emptyLocalsHOLFinite]
      all_goals split <;>
        simp [setKvarFfiHOLFinite,setKvarHOLFinite,setVarHOLFinite,emptyLocalsHOLFinite,
          HolFiniteMapExact.lookup_update,FUPDATE,ne_comm]
      all_goals intro key different equal; exact (different equal).elim
    · simp
  · simp

#print axioms evaluate_shared_load_control_frame
end InitECandidate.Runtime
