import InitECandidate.Runtime.RankedWhile
import InitECandidate.Runtime.NoTopBreak
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

theorem eval_localBound_less {F : Type} (state : PanSemStateFiniteExact 64 F) (counter bound : MlS) (op : Cmp)
    (hop : op = .less ∨ op = .lower) (w K : BitVec 64) (hw : w.toNat < 2 ^ 63) (hK : K.toNat < 2 ^ 63)
    (atCounter : state.locals.lookup counter = some (.val (.word w)))
    (atBound : state.locals.lookup bound = some (.val (.word K))) :
    evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      (.cmp op (.var .local counter) (.var .local bound)) =
      some (.val (.word (if w.toNat < K.toNat then 1 else 0))) := by
  rw [evalHOLFinite_eq_toExact]
  rcases hop with rfl | rfl
  · simp only [evalHOLExact,atCounter,atBound]
    simp only [Compiler.Encoders.Asm.wordCmpHOL,holAsmSignedLess_small w K hw hK]
    by_cases lt : w.toNat < K.toNat <;> simp [lt]
  · simp only [evalHOLExact,atCounter,atBound]
    simp only [Compiler.Encoders.Asm.wordCmpHOL]
    by_cases lt : w.toNat < K.toNat
    · simp [lt,BitVec.lt_def]
    · simp [lt,BitVec.lt_def]

theorem eval_localBound_notLowerAdd {F : Type} (state : PanSemStateFiniteExact 64 F) (counter bound : MlS)
    (w K step : BitVec 64) (fits : w.toNat + step.toNat < 2 ^ 64)
    (atCounter : state.locals.lookup counter = some (.val (.word w)))
    (atBound : state.locals.lookup bound = some (.val (.word K))) :
    evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      (.cmp .notLower (.var .local bound) (.op .add [.var .local counter,.const step])) =
      some (.val (.word (if w.toNat + step.toNat ≤ K.toNat then 1 else 0))) := by
  rw [evalHOLFinite_eq_toExact]
  simp only [evalHOLExact,evalListHOLExact,atCounter,atBound]
  simp [wordOpHOL,wordOp,valueIsWord,valueWord,Compiler.Encoders.Asm.wordCmpHOL]
  have natural : (w + step).toNat = w.toNat + step.toNat := BitVec.toNat_add_of_lt fits
  by_cases le : w.toNat + step.toNat ≤ K.toNat
  · rw [if_pos le,if_pos (by rw [BitVec.le_def,natural]; exact le)]
  · rw [if_neg le,if_neg (by rw [BitVec.le_def,natural]; exact le)]

/-- Loop tests comparing a counter against a bound held in another local:
`i < n` (signed or unsigned) and `n >=+ i + c`. -/
inductive LocalBoundTest (counter bound : MlS) (step : BitVec 64) : ExpHOL 64 → Prop
  | below (op : Cmp) (hop : op = .less ∨ op = .lower) :
      LocalBoundTest counter bound step (.cmp op (.var .local counter) (.var .local bound))
  | fits : LocalBoundTest counter bound step (.cmp .notLower (.var .local bound) (.op .add [.var .local counter,.const step]))

theorem LocalBoundTest.eval {counter bound : MlS} {step : BitVec 64} {condition : ExpHOL 64}
    (test : LocalBoundTest counter bound step condition) {F : Type} (state : PanSemStateFiniteExact 64 F)
    (w K : BitVec 64) (hw : w.toNat < 2 ^ 63) (hK : K.toNat < 2 ^ 63) (hstep : step.toNat < 2 ^ 63) (positive : 0 < step.toNat)
    (atCounter : state.locals.lookup counter = some (.val (.word w)))
    (atBound : state.locals.lookup bound = some (.val (.word K))) :
    ∃ v : BitVec 64, evalHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) condition =
        some (.val (.word v)) ∧ (v ≠ 0 → w.toNat < K.toNat) ∧ (v = 0 → K.toNat < w.toNat + step.toNat) ∧
        (K.toNat ≤ w.toNat → v = 0) := by
  cases test with
  | below op hop =>
    refine ⟨_,eval_localBound_less state counter bound op hop w K hw hK atCounter atBound,?_,?_,?_⟩
    · intro h; by_cases lt : w.toNat < K.toNat
      · exact lt
      · simp [lt] at h
    · intro h; by_cases lt : w.toNat < K.toNat
      · simp [lt] at h
      · omega
    · intro h; have : ¬ w.toNat < K.toNat := by omega
      simp [this]
  | fits =>
    refine ⟨_,eval_localBound_notLowerAdd state counter bound w K step (by omega) atCounter atBound,?_,?_,?_⟩
    · intro h; by_cases le : w.toNat + step.toNat ≤ K.toNat
      · omega
      · simp [le] at h
    · intro h; by_cases le : w.toNat + step.toNat ≤ K.toNat
      · simp [le] at h
      · omega
    · intro h; have : ¬ w.toNat + step.toNat ≤ K.toNat := by omega
      simp [this]

theorem ceilRank_step (K w c n : Nat) (hc : 0 < c) (lt : w < K) (h : (K - w + c - 1) / c ≤ n + 1) :
    (K - (w + c) + c - 1) / c ≤ n := by
  by_cases hw : w + c ≤ K
  · have split : K - w + c - 1 = (K - (w + c) + c - 1) + c := by omega
    rw [split,Nat.add_div_right _ hc] at h
    omega
  · have zero : K - (w + c) = 0 := by omega
    rw [zero,Nat.zero_add,(Nat.div_eq_zero_iff_lt hc).mpr (by omega)]
    exact Nat.zero_le _

theorem ceilRank_zero (K w c : Nat) (hc : 0 < c) (h : (K - w + c - 1) / c ≤ 0) : K ≤ w := by
  have : (K - w + c - 1) / c = 0 := Nat.le_zero.mp h
  have := (Nat.div_eq_zero_iff_lt hc).mp this
  omega

/-- The local-bound rank: the counter is a word below 2^63, the bound local
holds K, and at most `n` iterations remain (ceiling of (K - i) / c). -/
def LocalBoundRank (counter bound : MlS) (step K : BitVec 64) {F : Type} (s : PanSemStateFiniteExact 64 F) (n : Nat) : Prop :=
  ∃ w : BitVec 64, s.locals.lookup counter = some (.val (.word w)) ∧ s.locals.lookup bound = some (.val (.word K)) ∧
    w.toNat < 2 ^ 63 ∧ (K.toNat - w.toNat + step.toNat - 1) / step.toNat ≤ n

/-- A counted loop against a bound held in a local that the body never
rebinds: at most ceil((K - i) / c) iterations of `cost + 1` ticks, in every
outcome; a normal exit leaves the counter a word w < 2^63 with K < w + c. -/
theorem localBoundWhile_run (counter bound : MlS) (step K : BitVec 64) {condition : ExpHOL 64}
    (test : LocalBoundTest counter bound step condition) (small : K.toNat + step.toNat < 2 ^ 63)
    (positive : 0 < step.toNat) {body : ProgHOL 64} {cost : Nat}
    (counted : CountedBody counter step body cost) (keep : avoidsLocal bound body = true)
    (noBreak : noTopBreak body = true) {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) (w : BitVec 64)
    (atCounter : state.locals.lookup counter = some (.val (.word w)))
    (atBound : state.locals.lookup bound = some (.val (.word K))) (within : w.toNat < 2 ^ 63)
    (budget : (K.toNat - w.toNat + step.toNat - 1) / step.toNat * (cost + 1) ≤ state.clock) :
    state.clock ≤ (evaluateHOLFiniteState state (.while condition body)).2.clock +
        (K.toNat - w.toNat + step.toNat - 1) / step.toNat * (cost + 1) ∧
      (evaluateHOLFiniteState state (.while condition body)).2.clock ≤ state.clock ∧
      (evaluateHOLFiniteState state (.while condition body)).1 ≠ some .timeOut ∧
      ((evaluateHOLFiniteState state (.while condition body)).1 = none →
        (evaluateHOLFiniteState state (.while condition body)).2.code = state.code ∧
        ∃ w' : BitVec 64, (evaluateHOLFiniteState state (.while condition body)).2.locals.lookup counter = some (.val (.word w')) ∧
          (evaluateHOLFiniteState state (.while condition body)).2.locals.lookup bound = some (.val (.word K)) ∧
          K.toNat < w'.toNat + step.toNat ∧ w'.toNat < 2 ^ 63) := by
  have loop := rankedWhile_run condition body cost (LocalBoundRank counter bound step K) False
    (by
      intro F s ranked v hv
      obtain ⟨w,atC,atB,within,rank⟩ := ranked
      have done := ceilRank_zero K.toNat w.toNat step.toNat positive rank
      obtain ⟨v',ev,_,_,stop⟩ := test.eval s w K (by omega) (by omega) (by omega) positive atC atB
      rw [ev] at hv
      cases hv
      exact stop done)
    (by
      intro F s n v code' ranked hv nonzero budget'
      obtain ⟨w,atC,atB,within,rank⟩ := ranked
      obtain ⟨v',ev,go,_,_⟩ := test.eval s w K (by omega) (by omega) (by omega) positive atC atB
      rw [ev] at hv
      cases hv
      have lt := go nonzero
      have run := counted.run (decClockHOLFinite s) code' w atC (by change cost ≤ s.clock - 1; omega)
      have frame := evaluate_avoidsLocal_flowing bound body keep (decClockHOLFinite s)
      have broken := evaluate_noTopBreak body noBreak (decClockHOLFinite s)
      obtain ⟨r1,r2,r3,r4,r5⟩ := run
      refine ⟨r1,r2,r3,?_,?_⟩
      · intro flow
        rcases flow with normal | cont
        · obtain ⟨nextC,nextCode⟩ := r5 normal
          have natural : (w + step).toNat = w.toNat + step.toNat := BitVec.toNat_add_of_lt (by omega)
          refine ⟨n,le_refl _,⟨w + step,nextC,?_,by rw [natural]; omega,?_⟩,nextCode⟩
          · rw [frame (Or.inl normal)]; exact atB
          · rw [natural]; exact ceilRank_step K.toNat w.toNat step.toNat n positive lt rank
        · exact absurd cont r4
      · intro b; exact absurd b broken)
  obtain ⟨l1,l2,l3,l4⟩ := loop _ state code ⟨w,atCounter,atBound,within,le_refl _⟩ budget
  refine ⟨l1,l2,l3,fun normal => ?_⟩
  obtain ⟨m,⟨w',atC,atB,within',_⟩,postCode,exitCond⟩ := l4 normal
  refine ⟨postCode,w',atC,atB,?_,within'⟩
  rcases exitCond with zero | f
  · obtain ⟨v,ev,_,stopped,_⟩ := test.eval _ w' K (by omega) (by omega) (by omega) positive atC atB
    rw [ev] at zero
    cases zero
    exact stopped rfl
  · exact f.elim

#print axioms localBoundWhile_run
end InitECandidate.Runtime
