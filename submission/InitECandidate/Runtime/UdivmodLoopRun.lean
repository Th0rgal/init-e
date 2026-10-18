import InitECandidate.Runtime.UdivmodLoop
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual 64-step division loop: at most i clocks, no timeout when
enough clock is present, and normal exit leaves i = 0 with the invariant. -/
theorem evaluate_udivmodLoop {σ : Type} (base : PanSemStateFiniteExact 64 σ) (a b : BitVec 64)
    (s : PanSemStateFiniteExact 64 σ) (inv : UdivLoopInv base a b s) (ticks : udivLoopRank s ≤ s.clock) :
    ∃ result post, evaluateHOLFiniteState s udivmodLoop = (result, post) ∧
      s.clock ≤ post.clock + udivLoopRank s ∧ post.clock ≤ s.clock ∧ result ≠ some .timeOut ∧
      (result = none → UdivLoopInv base a b post ∧ udivLoopRank post = 0) ∧
      (∀ value, result ≠ some (.returned value)) := by
  have guard : ∀ state, UdivLoopInv base a b state →
      evalHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .less (.const 0) (.var .local (ofString "i"))) =
        some (.val (.word (if udivLoopRank state = 0 then 0 else 1))) := by
    rintro state ⟨q, r, i, L, shape, ha, hb, hq, hr, hi, bound, arith⟩
    have hs : state.locals.lookup (ofString "i") = some (.val (.word i)) := by rw [shape]; exact hi
    have rank : udivLoopRank state = i.toNat := by simp [udivLoopRank, hs]
    rw [rank]
    by_cases zero : i.toNat = 0
    · simp [evalHOLFinite, evalHOLExact, hs, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        Flapjack.Compiler.Encoders.Asm.holAsmSignedLess, zero]
    · simp [evalHOLFinite, evalHOLExact, hs, Flapjack.Compiler.Encoders.Asm.wordCmpHOL,
        Flapjack.Compiler.Encoders.Asm.holAsmSignedLess, zero]
      omega
  have entry : ∀ state, UdivLoopInv base a b state → UdivLoopInv base a b (decClockHOLFinite state) := by
    rintro state ⟨q, r, i, L, shape, rest⟩
    exact ⟨q, r, i, L, by rw [shape]; rfl, rest⟩
  have entryRank : ∀ state : PanSemStateFiniteExact 64 σ, udivLoopRank (decClockHOLFinite state) = udivLoopRank state := by
    intro state; rfl
  have step : ∀ state, UdivLoopInv base a b state → 0 < udivLoopRank state → 0 ≤ state.clock →
      ∃ post, state.clock ≤ post.clock + 0 ∧ post.clock ≤ state.clock ∧
        ((evaluateHOLFiniteState state udivmodStep = (none,post) ∧ UdivLoopInv base a b post ∧
            udivLoopRank post < udivLoopRank state) ∨
         (∃ result, result ≠ .continue ∧ result ≠ .timeOut ∧ result ≠ .break ∧ (∀ value, result ≠ .returned value) ∧
           evaluateHOLFiniteState state udivmodStep = (some result,post))) := by
    intro state inv positive _
    obtain ⟨run, next, smaller, clock⟩ := udivmodLoop_step base a b state inv positive
    exact ⟨_, by omega, by omega, Or.inl ⟨run, next, smaller⟩⟩
  have result := evaluate_ranked_loop_exits_invariant _ udivmodStep (UdivLoopInv base a b) udivLoopRank 0
    guard entry entryRank step s inv (by simpa using ticks)
  simpa [udivmodLoop] using result

#print axioms evaluate_udivmodLoop
end InitECandidate.Runtime
