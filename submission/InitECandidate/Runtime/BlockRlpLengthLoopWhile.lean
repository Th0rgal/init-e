import InitECandidate.Runtime.BlockRlpLengthLoopCounter
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
theorem blockRlpCountedWhile_run (counter limit : MlS) (op : Cmp)
    (hop : op = .less ∨ op = .lower) (K : BitVec 64)
    (signed : op = .less → K.toNat < 2 ^ 63)
    {body : ProgHOL 64} {cost : Nat} (counted : BlockRlpCountedBody counter body cost)
    (preservesLimit : avoidsLocal limit body = true) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F),
      state.code = originalRuntimeCode →
      ∀ w : BitVec 64, state.locals.lookup counter = some (.val (.word w)) →
      state.locals.lookup limit = some (.val (.word K)) → w.toNat ≤ K.toNat →
      K.toNat - w.toNat = n → n * (cost + 1) ≤ state.clock →
      let evaluated := evaluateHOLFiniteState state
        (.while (.cmp op (.var .local counter) (.var .local limit)) body)
      state.clock ≤ evaluated.2.clock + n * (cost + 1) ∧
        evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F state code w atCounter atLimit within distance budget
    have condition := eval_variable_counted_condition state counter limit op hop K w
      signed within atCounter atLimit
    dsimp only
    rw [evaluateHOLFiniteState_while_total,condition]
    by_cases lt : w.toNat < K.toNat
    · rw [if_pos lt]
      simp only [show (1 : BitVec 64) ≠ 0 by decide,if_true,ne_eq,not_false_eq_true]
      have positiveRank : 0 < n := by omega
      have oneIteration : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
      have clock : state.clock ≠ 0 := by omega
      rw [if_neg clock,fixClockHOLFinite_evaluateState]
      have stepRun := counted.run (decClockHOLFinite state) code w atCounter
        (by change cost ≤ state.clock - 1; omega)
      have frame := evaluate_avoidsLocal_flowing limit body preservesLimit (decClockHOLFinite state)
      cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
      | mk result middle =>
        rw [bodyRun] at stepRun frame
        dsimp only at stepRun frame
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
          have nextLimit : middle.locals.lookup limit = some (.val (.word K)) := by
            rw [frame (Or.inl rfl)]
            exact atLimit
          have tail := ih (K.toNat - (w + 1).toNat) nextRank middle (nextCode.trans code)
            (w + 1) nextCounter nextLimit (by rw [natural]; omega) rfl (by
              have decrease : (K.toNat - (w + 1).toNat) * (cost + 1) + (cost + 1) ≤ n * (cost + 1) := by
                rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
              omega)
          obtain ⟨t1,t2,t3⟩ := tail
          have decrease : (K.toNat - (w + 1).toNat) * (cost + 1) + (cost + 1) ≤ n * (cost + 1) := by
            rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
          exact ⟨by omega,by omega,t3⟩
        | some r =>
          cases r with
          | «continue» => exact absurd rfl noCont
          | «break» => exact ⟨by simp; omega,by simp; omega,by simp⟩
          | timeOut => exact absurd rfl safe
          | _ => exact ⟨by simp; omega,by simp; omega,by simp⟩
    · rw [if_neg lt]
      simp

/-- A zero-start loop has a finite bound for every 64-bit limit. A negative
signed limit skips the loop; otherwise its natural value bounds iterations. -/
theorem blockRlpCountedWhile_zero_bounded {F : Type}
    (counter limit : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower)
    {body : ProgHOL 64} {cost : Nat} (counted : BlockRlpCountedBody counter body cost)
    (preservesLimit : avoidsLocal limit body = true)
    (state : PanSemStateFiniteExact 64 F) (code : state.code = originalRuntimeCode)
    (K : BitVec 64)
    (atCounter : state.locals.lookup counter = some (.val (.word 0)))
    (atLimit : state.locals.lookup limit = some (.val (.word K)))
    (budget : (2 ^ 64 - 1) * (cost + 1) ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state
      (.while (.cmp op (.var .local counter) (.var .local limit)) body)
    state.clock ≤ evaluated.2.clock + (2 ^ 64 - 1) * (cost + 1) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  by_cases signed : op = .less → K.toNat < 2 ^ 63
  · have ceiling : K.toNat * (cost + 1) ≤ (2 ^ 64 - 1) * (cost + 1) :=
      Nat.mul_le_mul_right _ (by have bound := K.isLt; omega)
    have bounded := blockRlpCountedWhile_run counter limit op hop K signed counted preservesLimit
      K.toNat state code 0 atCounter atLimit (by simp) (by simp) (by omega)
    dsimp only at bounded ⊢
    exact ⟨by omega,bounded.2.1,bounded.2.2⟩
  · have comparison : op = .less := by
      rcases hop with eq | eq
      · exact eq
      · exfalso
        apply signed
        intro impossible
        cases eq.symm.trans impossible
    have negative : ¬ K.toNat < 9223372036854775808 := by
      intro small
      exact signed (fun _ => small)
    subst op
    have condition : evalHOLFinite state
        (h := fun a => Classical.propDecidable (state.memaddrs a))
        (.cmp .less (.var .local counter) (.var .local limit)) = some (.val (.word 0)) := by
      rw [evalHOLFinite_eq_toExact]
      simp [evalHOLExact,atCounter,atLimit,Compiler.Encoders.Asm.wordCmpHOL,
        Compiler.Encoders.Asm.holAsmSignedLess,negative]
    dsimp only
    rw [evaluateHOLFiniteState_while_total,condition]
    simp

#print axioms blockRlpCountedWhile_run
#print axioms blockRlpCountedWhile_zero_bounded
end InitECandidate.Runtime
