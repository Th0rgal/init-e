import InitECandidate.Runtime.HtabFindSlotReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
set_option maxRecDepth 100000
set_option maxHeartbeats 800000
theorem while_returned_active_invariant (condition : ExpHOL 64) (body : ProgHOL 64)
    (Inv : ∀ {F : Type}, PanSemStateFiniteExact 64 F → Prop) (P : ValueHOL 64 → Prop)
    (clockFree : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F), Inv s → Inv (decClockHOLFinite s))
    (returns : ∀ {F : Type} (s : PanSemStateFiniteExact 64 F) v post, Inv s →
      (∃ active : BitVec 64, evalHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a)) condition =
        some (.val (.word active)) ∧ active ≠ 0) →
      evaluateHOLFiniteState s body = (some (.returned v),post) → P v)
    (keeps : ∀ {F : Type} (s post : PanSemStateFiniteExact 64 F), Inv s →
      (evaluateHOLFiniteState s body = (none,post) ∨ evaluateHOLFiniteState s body = (some .continue,post)) → Inv post) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.clock = n → Inv state →
      ∀ v post, evaluateHOLFiniteState state (.while condition body) = (some (.returned v),post) → P v := by
  classical
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F state clock invariant v post run
    rw [evaluateHOLFiniteState_while_total] at run
    split at run
    · rename_i activeWord activeEval
      split at run
      · rename_i activeNonzero
        split at run
        · simp at run
        · rename_i nonzero
          dsimp only at run
          rw [fixClockHOLFinite_evaluateState] at run
          have remaining := evaluateHOLFiniteState_clock_le (decClockHOLFinite state) body
          cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
          | mk r mid =>
            rw [bodyRun] at run remaining
            have smaller : mid.clock < n := by
              change mid.clock ≤ state.clock - 1 at remaining
              omega
            cases r with
            | none =>
              exact ih mid.clock (by omega) mid rfl (keeps _ mid (clockFree state invariant) (Or.inl bodyRun)) v post run
            | some r =>
              cases r with
              | «continue» =>
                exact ih mid.clock (by omega) mid rfl (keeps _ mid (clockFree state invariant) (Or.inr bodyRun)) v post run
              | returned w =>
                simp at run
                obtain ⟨rfl,_⟩ := run
                exact returns _ w mid (clockFree state invariant) ⟨activeWord,by rw [evalHOLFinite_eq_toExact]; change evalHOLExact {state.toExact with clock := state.clock - 1} condition = _; rw [evalHOLExact_upd_clock_eq]; exact activeEval,activeNonzero⟩ bodyRun
              | _ => simp at run
      · simp at run
    · simp at run

#print axioms while_returned_active_invariant
end InitECandidate.Runtime
