import InitECandidate.Runtime.WordPathAffineControl
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.WordSemStateFiniteExact

/-- A continuing iteration pays one source clock before re-entry, which funds the
loop body's syntax potential. -/
theorem wordPath_loop_affine {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (names exits : WordLangNumSetHOL) (body : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F)
    (small : sizeOf (.loop names body exits : WordLangProgHOL (BitVec width)) ≤ limit)
    (bounded : WordCodeSize limit s) (safe : noInstallSubprogsHOL (.loop names body exits) = true)
    (ih : WordAffineIH limit (.loop names body exits) s) :
    WordAffine (2 * limit + 2) (.loop names body exits) s := by
  have bodySize : sizeOf body < sizeOf (.loop names body exits : WordLangProgHOL (BitVec width)) := by
    simp_wf
    omega
  have bodySafe : noInstallSubprogsHOL body = true := by
    simpa [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] using safe
  have positive := word_prog_size_positive (.loop names body exits : WordLangProgHOL (BitVec width))
  intro result post run
  rw [WordSemStateFiniteExact.evaluate] at run
  rw [wordPathWork]
  split
  · omega
  · rename_i cutSource cut
    rw [cut] at run
    have sameClock := (cutState_clock_termdep _ _ _ cut).1
    have cutBound := bounded.cutState _ cut
    have first := ih body cutSource (workRank_subprogram _ _ _ _ _ (by omega) bodySize)
      (by omega) cutBound bodySafe
    dsimp only at run
    rw [fix_clock_evaluate] at run ⊢
    cases bodyRun : evaluate body cutSource with
    | mk bodyResult middle =>
      rw [bodyRun] at run
      dsimp only at run ⊢
      have bodyBound := first bodyResult middle bodyRun
      rw [sameClock] at bodyBound
      have lower := (evaluate_clock body cutSource bodyResult middle bodyRun).1
      have middleBound : WordCodeSize limit middle := by
        have next := cutBound.evaluated body bodySafe
        rwa [fix_clock_evaluate, bodyRun] at next
      by_cases continuing : wordSemContLoop bodyResult = true
      · rw [if_pos continuing] at run ⊢
        by_cases zero : middle.clock = 0
        · rw [dif_pos zero] at run ⊢
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj run
          simp only [flushState]
          omega
        · rw [dif_neg zero] at run ⊢
          have strict : (decClock middle).clock < s.clock := by
            simp only [decClock]
            omega
          have rest := ih (.loop names body exits) (decClock middle)
            (workRank_clock _ _ _ _ _ strict small) small middleBound.decClock safe result post run
          have restClock := (evaluate_clock _ _ result post run).1
          have decremented : (decClock middle).clock = middle.clock - 1 := rfl
          rw [decremented] at rest restClock
          have split : s.clock - post.clock =
              (s.clock - middle.clock) + 1 + (middle.clock - 1 - post.clock) := by omega
          rw [split, Nat.mul_add, Nat.mul_add, Nat.mul_one]
          try simp only [wordSemSTOP]
          omega
      · rw [if_neg continuing] at run ⊢
        have postClock : post.clock = middle.clock := by
          cases bodyResult with
          | none => simp [wordSemContLoop] at continuing
          | some r =>
            cases r
            all_goals try (dsimp only at run; obtain ⟨-, rfl⟩ := Prod.mk.inj run; rfl)
            rename_i n
            cases n with
            | zero =>
              try dsimp only at run
              split at run
              · cases exitCut : cutState (exits, .ln) middle with
                | none =>
                  simp only [exitCut] at run
                  obtain ⟨-, rfl⟩ := Prod.mk.inj run; rfl
                | some s2 =>
                  simp only [exitCut] at run
                  obtain ⟨-, rfl⟩ := Prod.mk.inj run
                  exact (cutState_clock_termdep _ _ _ exitCut).1
              · rename_i bad
                exact absurd rfl bad
            | succ n => try dsimp only at run
                        obtain ⟨-, rfl⟩ := Prod.mk.inj run; rfl
        rw [postClock]
        omega

#print axioms wordPath_loop_affine
end InitECandidate.Runtime.WordToStack
