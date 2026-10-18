import InitECandidate.Runtime.NestedCountedBody
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
/-- A counted while loop `while i < K { body; i = i + c }` (signed or unsigned
comparison, K + c < 2^63) runs at most K - i iterations from any counter value
i ≤ K + c, in every outcome. -/
theorem nestedCountedWhile_run (counter : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower) (K step : BitVec 64)
    (small : K.toNat + step.toNat < 2 ^ 63) (positive : 0 < step.toNat) {body : ProgHOL 64} {cost : Nat}
    (counted : NestedCountedBody counter step body cost) :
    ∀ n : Nat, ∀ {F : Type} (state : PanSemStateFiniteExact 64 F), state.code = originalRuntimeCode →
      ∀ w : BitVec 64, state.locals.lookup counter = some (.val (.word w)) → w.toNat ≤ K.toNat + step.toNat →
      K.toNat - w.toNat = n → n * (cost + 1) ≤ state.clock →
      state.clock ≤ (evaluateHOLFiniteState state (.while (.cmp op (.var .local counter) (.const K)) body)).2.clock + n * (cost + 1) ∧
        (evaluateHOLFiniteState state (.while (.cmp op (.var .local counter) (.const K)) body)).2.clock ≤ state.clock ∧
        (evaluateHOLFiniteState state (.while (.cmp op (.var .local counter) (.const K)) body)).1 ≠ some .timeOut := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro F state code w atCounter within distance budget
    have condition := eval_counted_condition state counter op hop K w (by omega) (by omega) atCounter
    rw [evaluateHOLFiniteState_while_total,condition]
    by_cases lt : w.toNat < K.toNat
    · rw [if_pos lt]
      simp only [show (1 : BitVec 64) ≠ 0 by decide,if_true,ne_eq,not_false_eq_true]
      have positiveRank : 0 < n := by omega
      have clock : state.clock ≠ 0 := by
        have : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
        omega
      rw [if_neg clock]
      rw [fixClockHOLFinite_evaluateState]
      have stepRun := counted.run (decClockHOLFinite state) code w atCounter (by
        change cost ≤ state.clock - 1
        have : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
        omega)
      have meta' := evaluateHOLFiniteState_metadata (decClockHOLFinite state) body
      cases bodyRun : evaluateHOLFiniteState (decClockHOLFinite state) body with
      | mk result middle =>
        rw [bodyRun] at stepRun meta'
        dsimp only at stepRun meta'
        obtain ⟨spent,kept,safe,noCont,advance⟩ := stepRun
        change state.clock - 1 ≤ middle.clock + cost at spent
        change middle.clock ≤ state.clock - 1 at kept
        have oneIteration : cost + 1 ≤ n * (cost + 1) := Nat.le_mul_of_pos_left _ positiveRank
        cases result with
        | none =>
          dsimp only
          obtain ⟨nextCounter,nextCode⟩ := advance rfl
          have natural : (w + step).toNat = w.toNat + step.toNat := by
            rw [BitVec.toNat_add_of_lt (by omega)]
          have nextRank : K.toNat - (w + step).toNat < n := by rw [natural]; omega
          have tail := ih (K.toNat - (w + step).toNat) nextRank middle (nextCode.trans code) (w + step) nextCounter
            (by rw [natural]; omega) rfl (by
              have : (K.toNat - (w + step).toNat) * (cost + 1) + (cost + 1) ≤ n * (cost + 1) := by
                rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
              omega)
          obtain ⟨t1,t2,t3⟩ := tail
          refine ⟨?_,by omega,t3⟩
          have : (K.toNat - (w + step).toNat) * (cost + 1) + (cost + 1) ≤ n * (cost + 1) := by
            rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (by omega)
          omega
        | some r =>
          cases r with
          | «continue» => exact absurd rfl noCont
          | «break» => exact ⟨by simp; omega,by simp; omega,by simp⟩
          | timeOut => exact absurd rfl safe
          | _ => exact ⟨by simp; omega,by simp; omega,by simp⟩
    · rw [if_neg lt]
      simp

#print axioms nestedCountedWhile_run
/-- The counted loop from a state whose counter is a word at most K, as a
uniform bound with cost K * (cost + 1). -/
theorem nestedCountedWhile_from {F : Type} (counter : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower) (K step : BitVec 64)
    (small : K.toNat + step.toNat < 2 ^ 63) (positive : 0 < step.toNat) {body : ProgHOL 64} {cost : Nat}
    (counted : NestedCountedBody counter step body cost) (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) (w : BitVec 64)
    (atCounter : state.locals.lookup counter = some (.val (.word w))) (within : w.toNat ≤ K.toNat)
    (budget : K.toNat * (cost + 1) ≤ state.clock) :
    state.clock ≤ (evaluateHOLFiniteState state (.while (.cmp op (.var .local counter) (.const K)) body)).2.clock + K.toNat * (cost + 1) ∧
      (evaluateHOLFiniteState state (.while (.cmp op (.var .local counter) (.const K)) body)).2.clock ≤ state.clock ∧
      (evaluateHOLFiniteState state (.while (.cmp op (.var .local counter) (.const K)) body)).1 ≠ some .timeOut := by
  have mono : (K.toNat - w.toNat) * (cost + 1) ≤ K.toNat * (cost + 1) := Nat.mul_le_mul_right _ (by omega)
  obtain ⟨a,b,c⟩ := nestedCountedWhile_run counter op hop K step small positive counted (K.toNat - w.toNat) state code w
    atCounter (by omega) rfl (by omega)
  exact ⟨by omega,b,c⟩

/-- `var i = s; while i < K { ... i = i + c }; tail` in the declaration form produced
by the frontend. -/
theorem ProgBounded.nestedCountedDec (counter : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower) (K step start : BitVec 64)
    (small : K.toNat + step.toNat < 2 ^ 63) (positive : 0 < step.toNat) (begin : start.toNat ≤ K.toNat)
    {body tail : ProgHOL 64} {cost tailCost : Nat} (counted : NestedCountedBody counter step body cost)
    (rest : ProgBounded tail tailCost) :
    ProgBounded (.dec counter .one (.const start) (.seq (.while (.cmp op (.var .local counter) (.const K)) body) tail))
      (K.toNat * (cost + 1) + tailCost) := by
  intro F state code budget
  rw [evaluateHOLFiniteState_dec_total]
  simp only [evalHOLExact,shapeOfHOLExact,shapeEqHOL,if_true]
  let entered := setVarHOLFinite counter (.val (.word start)) state
  have atCounter : entered.locals.lookup counter = some (.val (.word start)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have loop := nestedCountedWhile_from counter op hop K step small positive counted entered code start atCounter begin
    (by change K.toNat * (cost + 1) ≤ state.clock; omega)
  have meta' := evaluateHOLFiniteState_metadata entered (.while (.cmp op (.var .local counter) (.const K)) body)
  change state.clock ≤ (evaluateHOLFiniteState entered _).2.clock + _ ∧
    (evaluateHOLFiniteState entered _).2.clock ≤ state.clock ∧ (evaluateHOLFiniteState entered _).1 ≠ some .timeOut
  rw [evaluateHOLFiniteState_seq_line780]
  cases loopRun : evaluateHOLFiniteState entered (.while (.cmp op (.var .local counter) (.const K)) body) with
  | mk result middle =>
    rw [loopRun] at loop meta'
    dsimp only at loop meta'
    obtain ⟨spent,kept,safe⟩ := loop
    change state.clock ≤ middle.clock + K.toNat * (cost + 1) at spent
    change middle.clock ≤ state.clock at kept
    cases result with
    | none =>
      dsimp only
      obtain ⟨t1,t2,t3⟩ := rest middle (meta'.1.trans code) (by omega)
      exact ⟨by omega,by omega,t3⟩
    | some r =>
      dsimp only
      exact ⟨by omega,kept,safe⟩

/-- `i = s; while i < K { ... i = i + c }; tail` with an assignment initializer. -/
theorem ProgBounded.nestedCountedAssign (counter : MlS) (op : Cmp) (hop : op = .less ∨ op = .lower) (K step start : BitVec 64)
    (small : K.toNat + step.toNat < 2 ^ 63) (positive : 0 < step.toNat) (begin : start.toNat ≤ K.toNat)
    {body tail : ProgHOL 64} {cost tailCost : Nat} (counted : NestedCountedBody counter step body cost)
    (rest : ProgBounded tail tailCost) :
    ProgBounded (.seq (.assign .local counter (.const start)) (.seq (.while (.cmp op (.var .local counter) (.const K)) body) tail))
      (K.toNat * (cost + 1) + tailCost) := by
  intro F state code budget
  by_cases valid : isValidValueHOLExact state.toExact .local counter (.val (.word start)) = true
  · have assignRun : evaluateHOLFiniteState state (.assign .local counter (.const start)) =
        (none,setKvarHOLFinite .local counter (.val (.word start)) state) := by
      simp [evaluateHOLFiniteState_assign,evalHOLExact,valid]
    rw [evaluateHOLFiniteState_seq_line780,assignRun]
    dsimp only
    let entered := setKvarHOLFinite .local counter (.val (.word start)) state
    have atCounter : entered.locals.lookup counter = some (.val (.word start)) := by
      simp [entered,setKvarHOLFinite,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have enteredCode : entered.code = originalRuntimeCode := code
    have loop := nestedCountedWhile_from counter op hop K step small positive counted entered enteredCode start atCounter begin
      (by change K.toNat * (cost + 1) ≤ state.clock; omega)
    have meta' := evaluateHOLFiniteState_metadata entered (.while (.cmp op (.var .local counter) (.const K)) body)
    change state.clock ≤ (evaluateHOLFiniteState entered _).2.clock + _ ∧
      (evaluateHOLFiniteState entered _).2.clock ≤ state.clock ∧ (evaluateHOLFiniteState entered _).1 ≠ some .timeOut
    rw [evaluateHOLFiniteState_seq_line780]
    cases loopRun : evaluateHOLFiniteState entered (.while (.cmp op (.var .local counter) (.const K)) body) with
    | mk result middle =>
      rw [loopRun] at loop meta'
      dsimp only at loop meta'
      obtain ⟨spent,kept,safe⟩ := loop
      change state.clock ≤ middle.clock + K.toNat * (cost + 1) at spent
      change middle.clock ≤ state.clock at kept
      cases result with
      | none =>
        dsimp only
        obtain ⟨t1,t2,t3⟩ := rest middle (meta'.1.trans code) (by omega)
        exact ⟨by omega,by omega,t3⟩
      | some r =>
        dsimp only
        exact ⟨by omega,kept,safe⟩
  · have assignRun : evaluateHOLFiniteState state (.assign .local counter (.const start)) = (some .error,state) := by
      simp [evaluateHOLFiniteState_assign,evalHOLExact,valid]
    rw [evaluateHOLFiniteState_seq_line780,assignRun]
    simp

#print axioms ProgBounded.nestedCountedDec
#print axioms ProgBounded.nestedCountedAssign
end InitECandidate.Runtime
