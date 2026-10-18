import InitECandidate.Runtime.CountedLoop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- A guard that stops or rejects at a fixed counter value suffices for a
counted-loop bound. It need not compare the counter directly with that value. -/
theorem cappedCountedWhile_run (counter : MlS) (condition : ExpHOL 64) (K : BitVec 64)
    (stop : ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
      state.locals.lookup counter = some (.val (.word K)) →
      evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) condition = none ∨
      evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) condition = some (.val (.word (0#64))))
    {body : ProgHOL 64} {cost : Nat} (counted : CountedBody counter 1 body cost) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode →
      ∀ w : BitVec 64, state.locals.lookup counter = some (.val (.word w)) →
      w.toNat ≤ K.toNat → K.toNat - w.toNat = n → n * (cost + 1) ≤ state.clock →
      let evaluated := evaluateHOLFiniteState state (.while condition body)
      state.clock ≤ evaluated.2.clock + n * (cost + 1) ∧
        evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F state code w atCounter within distance budget
    dsimp only
    rw [evaluateHOLFiniteState_while_total]
    cases guardRun : evalHOLFinite state
        (h := fun a => Classical.propDecidable (state.memaddrs a)) condition with
    | none => simp
    | some value =>
      cases value with
      | rStruct fields => simp
      | nStruct name fields => simp
      | val word =>
        cases word with
        | word test =>
          by_cases zero : test = (0#64)
          · simp [zero]
          · simp only [zero,if_false]
            have lt : w.toNat < K.toNat := by
              by_contra notLt
              have same : w = K := BitVec.eq_of_toNat_eq (by omega)
              have ended := stop state (by simpa only [same] using atCounter)
              rcases ended with rejected | finished
              · rw [guardRun] at rejected
                cases rejected
              · rw [guardRun] at finished
                have equal : test = (0#64) := by cases finished; rfl
                exact zero equal
            have positiveRank : 0 < n := by omega
            have oneIteration : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
            have clock : state.clock ≠ 0 := by omega
            rw [if_neg clock,fixClockHOLFinite_evaluateState]
            simp only [zero,ne_eq,not_false_eq_true,if_true,if_false]
            have stepRun := counted.run (decClockHOLFinite state) code w atCounter
              (by change cost ≤ state.clock - 1; omega)
            cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
            | mk result middle =>
              rw [bodyRun] at stepRun
              dsimp only at stepRun
              obtain ⟨spent,kept,safe,noCont,advance⟩ := stepRun
              change state.clock - 1 ≤ middle.clock + cost at spent
              change middle.clock ≤ state.clock - 1 at kept
              cases result with
              | none =>
                dsimp only
                obtain ⟨nextCounter,nextCode⟩ := advance rfl
                have natural : (w + 1).toNat = w.toNat + 1 := by
                  rw [BitVec.toNat_add_of_lt (by have bound := K.isLt; simp; omega)]
                  rfl
                have nextRank : K.toNat - (w + 1).toNat < n := by rw [natural]; omega
                have decrease : (K.toNat - (w + 1).toNat) * (cost + 1) + (cost + 1) ≤ n * (cost + 1) := by
                  rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
                have tail := ih (K.toNat - (w + 1).toNat) nextRank middle (nextCode.trans code)
                  (w + 1) nextCounter (by rw [natural]; omega) rfl (by omega)
                obtain ⟨t1,t2,t3⟩ := tail
                simp [zero]
                exact ⟨by omega,by omega,t3⟩
              | some r =>
                cases r with
                | «continue» => exact absurd rfl noCont
                | «break» => exact ⟨by simp [zero]; omega,by simp [zero]; omega,by simp [zero]⟩
                | timeOut => exact absurd rfl safe
                | _ => exact ⟨by simp [zero]; omega,by simp [zero]; omega,by simp [zero]⟩

#print axioms cappedCountedWhile_run
end InitECandidate.Runtime
