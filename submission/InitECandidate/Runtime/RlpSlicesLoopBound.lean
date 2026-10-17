import InitECandidate.Runtime.RlpSlicesLoopInvariant
import InitECandidate.Runtime.RlpSlicesStepBound
import InitECandidate.Runtime.RlpSlicesStepControl
import InitECandidate.Runtime.RankedLoopExitsInvariant
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The complete original slice loop uses at most twelve ticks per remaining
slice. All read/store failures terminate within the same bound. -/
theorem evaluate_rlpSlices_loop_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer count : BitVec 64) (valid : RlpSlicesLoopWitness state pointer count)
    (budget : (count.toNat - valid.index.toNat) * 12 ≤ state.clock) :
    ∃ result post, evaluateHOLFiniteState state rlpSlicesLoop = (result,post) ∧
      state.clock ≤ post.clock + (count.toNat - valid.index.toNat) * 12 ∧
      post.clock ≤ state.clock ∧ result ≠ some .timeOut ∧
      (result = none → ∃ _next : RlpSlicesLoopWitness post pointer count,
        post.locals.lookup (ofString "i") = some (.val (.word count))) ∧
      (∀ value, result ≠ some (.returned value)) := by
  let invariant := fun current : PanSemStateFiniteExact 64 F => Nonempty (RlpSlicesLoopWitness current pointer count)
  let cost := 11
  have rankEq : ∀ (current : PanSemStateFiniteExact 64 F) (witness : RlpSlicesLoopWitness current pointer count),
      rlpSlicesRank count current = count.toNat - witness.index.toNat := by
    intro current witness
    simp [rlpSlicesRank,witness.indexLocal]
  have guard : ∀ current, invariant current → evalHOLFinite current
      (h := fun address => Classical.propDecidable (current.memaddrs address))
      (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "count"))) =
      some (.val (.word (if rlpSlicesRank count current = 0 then 0 else 1))) := by
    rintro current ⟨witness⟩
    by_cases inside : witness.index.toNat < count.toNat
    · have nonzero : rlpSlicesRank count current ≠ 0 := by rw [rankEq current witness]; omega
      simp [evalHOLFinite,evalHOLExact,witness.indexLocal,witness.countLocal,
        Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,inside,nonzero]
    · have zero : rlpSlicesRank count current = 0 := by rw [rankEq current witness]; omega
      simp [evalHOLFinite,evalHOLExact,witness.indexLocal,witness.countLocal,
        Compiler.Encoders.Asm.wordCmpHOL,BitVec.lt_def,inside,zero]
  have enter : ∀ current, invariant current → invariant (decClockHOLFinite current) := by
    rintro current ⟨witness⟩
    exact ⟨witness.decClock⟩
  have entryRank : ∀ current : PanSemStateFiniteExact 64 F,
      rlpSlicesRank count (decClockHOLFinite current) = rlpSlicesRank count current := by intro current; rfl
  have step : ∀ current, invariant current → 0 < rlpSlicesRank count current → cost ≤ current.clock →
      ∃ post, current.clock ≤ post.clock + cost ∧ post.clock ≤ current.clock ∧
        ((evaluateHOLFiniteState current rlpSlicesStep = (none,post) ∧ invariant post ∧
          rlpSlicesRank count post < rlpSlicesRank count current) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧
           (∀ value, result ≠ .returned value) ∧ evaluateHOLFiniteState current rlpSlicesStep = (some result,post))) := by
    rintro current ⟨witness⟩ positive ticks
    have bounded := evaluate_rlpSlices_step_bounded current pointer witness.offset witness.pointerLocal witness.offsetLocal witness.code ticks
    have control := evaluate_rlpSlices_step_control current
    cases run : evaluateHOLFiniteState current rlpSlicesStep with
    | mk result post =>
      rw [run] at bounded control
      refine ⟨post,bounded.1,bounded.2.1,?_⟩
      cases result with
      | none =>
        obtain ⟨next,decreases⟩ := rlpSlices_loop_witness_step current post pointer count witness (by assumption) run
        exact Or.inl ⟨rfl,⟨next⟩,decreases⟩
      | some result =>
        refine Or.inr ⟨result,?_,?_,?_,?_,rfl⟩
        · intro equal; subst result; exact control.2.1 rfl
        · intro equal; subst result; exact bounded.2.2 rfl
        · intro equal; subst result; exact control.1 rfl
        · intro value equal; subst result; exact control.2.2 value rfl
  obtain ⟨result,post,run,total,remaining,noTimeout,done,noReturn⟩ := evaluate_ranked_loop_exits_invariant
    (.cmp .lower (.var .local (ofString "i")) (.var .local (ofString "count"))) rlpSlicesStep
    invariant (rlpSlicesRank count) cost guard enter entryRank step state ⟨valid⟩
    (by simpa only [rankEq state valid,cost] using budget)
  refine ⟨result,post,?_,?_,remaining,noTimeout,?_,noReturn⟩
  · rw [source_rlpSlices_loop]; exact run
  · simpa only [rankEq state valid,cost] using total
  · intro normal
    obtain ⟨⟨next⟩,zero⟩ := done normal
    have same : next.index = count := by
      apply BitVec.eq_of_toNat_eq
      rw [rankEq post next] at zero
      have bounded := next.indexBound
      omega
    exact ⟨next,by simpa [same] using next.indexLocal⟩

#print axioms evaluate_rlpSlices_loop_bounded
end InitECandidate.Runtime
