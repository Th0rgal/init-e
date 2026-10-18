import InitECandidate.Runtime.WordPathAffineLoop
import InitECandidate.Runtime.WordWorkCeilingReturning
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.WordSemStateFiniteExact

/-- Syntax size of an optional installed exception handler body. -/
noncomputable def wordHandlerSize {width : Nat} [NeZero width]
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat)) : Nat :=
  match handler with
  | none => 0
  | some (_, hp, _, _) => sizeOf hp

/-- A tail call spends one source clock before its bounded selected body. -/
theorem wordPath_tail_affine {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) (bounded : WordCodeSize limit s)
    (ih : WordAffineIH limit (.call none dest args handler) s) :
    WordAffine (2 * limit + 2) (.call none dest args handler) s := by
  have positive := word_prog_size_positive (.call none dest args handler : WordLangProgHOL (BitVec width))
  intro result post run
  rw [WordSemStateFiniteExact.evaluate] at run
  rw [wordPathWork]
  split
  · omega
  · rename_i values vars
    rw [vars] at run
    dsimp only at run
    by_cases bad : wordSemBadDestArgs dest args = true
    · rw [if_pos bad]
      omega
    · rw [if_neg bad]
      rw [if_neg bad] at run
      split
      · omega
      · rename_i foundArgs body ss found
        rw [found] at run
        dsimp only at run ⊢
        cases handler with
        | some handler => simp only; omega
        | none =>
          dsimp only at run ⊢
          split_ifs with zero
          · omega
          · rw [dif_neg zero] at run
            have selected := bounded.findCode dest values foundArgs body ss found
            have strict : (callEnv foundArgs ss (decClock s)).clock < s.clock := by
              simp only [Flapjack.WordSemStateFiniteExact.callEnv, decClock]
              omega
            have child := ih body (callEnv foundArgs ss (decClock s))
              (workRank_clock _ _ _ _ _ strict selected.1) selected.1
              (bounded.decClock.callEnv foundArgs ss) selected.2
            cases bodyRun : evaluate body (callEnv foundArgs ss (decClock s)) with
            | mk bodyResult middle =>
              rw [bodyRun] at run
              dsimp only at run
              have postEq : post = middle := by
                split at run <;> exact ((Prod.mk.inj run).2).symm
              subst postEq
              have bound := child bodyResult post bodyRun
              have entryClock : (callEnv foundArgs ss (decClock s)).clock = s.clock - 1 := rfl
              have lower := (evaluate_clock _ _ bodyResult post bodyRun).1
              rw [entryClock] at bound lower
              have split : s.clock - post.clock = 1 + (s.clock - 1 - post.clock) := by omega
              rw [split, Nat.mul_add, Nat.mul_one]
              omega

#print axioms wordPath_tail_affine

/-- A returning call spends one source clock; the callee and only its reached
valid continuation consume the rest. -/
theorem wordPath_return_affine {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F)
    (small : sizeOf (.call (some (values,names,retCode,l1,l2)) dest args handler : WordLangProgHOL (BitVec width)) ≤ limit)
    (bounded : WordCodeSize limit s)
    (safe : noInstallSubprogsHOL (.call (some (values,names,retCode,l1,l2)) dest args handler) = true)
    (ih : WordAffineIH limit (.call (some (values,names,retCode,l1,l2)) dest args handler) s) :
    WordAffine (2 * limit + 2) (.call (some (values,names,retCode,l1,l2)) dest args handler) s := by
  have positive := word_prog_size_positive
    (.call (some (values,names,retCode,l1,l2)) dest args handler : WordLangProgHOL (BitVec width))
  have retSize : sizeOf retCode < sizeOf (.call (some (values,names,retCode,l1,l2)) dest args handler :
      WordLangProgHOL (BitVec width)) := by simp_wf; omega
  have retSmall : sizeOf retCode ≤ limit := by omega
  have retSafe := noInstall_call_ret safe
  intro result post run
  rw [WordSemStateFiniteExact.evaluate] at run
  rw [wordPathWork]
  split
  · omega
  · rename_i xs vars
    rw [vars] at run
    dsimp only at run
    by_cases bad : wordSemBadDestArgs dest args = true
    · rw [if_pos bad]
      omega
    · rw [if_neg bad]
      rw [if_neg bad] at run
      split
      · omega
      · rename_i foundArgs body ss found
        rw [found] at run
        dsimp only at run ⊢
        by_cases invalid : sptDomainEmpty names.1 ∨ ¬values.Nodup
        · rw [if_pos invalid]
          omega
        · rw [if_neg invalid]
          rw [if_neg invalid] at run
          split
          · omega
          · rename_i envs cut
            rw [cut] at run
            dsimp only at run
            by_cases zero : s.clock = 0
            · rw [dif_pos zero]
              omega
            · rw [dif_neg zero]
              rw [dif_neg zero] at run
              have selected := bounded.findCode dest (wordSemAddRetLoc (some (values,names,retCode,l1,l2)) xs) foundArgs body ss found
              have entryClock : (callEnv foundArgs ss (pushEnv envs handler (decClock s))).clock = s.clock - 1 := by
                simp only [Flapjack.WordSemStateFiniteExact.callEnv, pushEnv_clock, decClock]
              have strict : (callEnv foundArgs ss (pushEnv envs handler (decClock s))).clock < s.clock := by
                omega
              have entryBound : WordCodeSize limit (callEnv foundArgs ss (pushEnv envs handler (decClock s))) :=
                (bounded.decClock.pushEnv envs handler).callEnv foundArgs ss
              have first := ih body _ (workRank_clock _ _ _ _ _ strict selected.1)
                selected.1 entryBound selected.2
              have nextBound := entryBound.evaluated body selected.2
              rw [fix_clock_evaluate] at nextBound
              -- One clock for the call, the callee consumption, then the continuation.
              have finish : ∀ (bodyResult : Option (WordSemResult width)) (middle : WordSemStateFiniteExact width C F),
                  evaluate body (callEnv foundArgs ss (pushEnv envs handler (decClock s))) = (bodyResult, middle) →
                  post.clock ≤ middle.clock →
                  ∀ extra, extra ≤ (2 * limit + 2) * (middle.clock - post.clock) + 2 * sizeOf retCode +
                      2 * wordHandlerSize handler →
                  1 + wordPathWork body (callEnv foundArgs ss (pushEnv envs handler (decClock s))) + extra ≤
                    (2 * limit + 2) * (s.clock - post.clock) +
                      2 * sizeOf (.call (some (values,names,retCode,l1,l2)) dest args handler : WordLangProgHOL (BitVec width)) := by
                intro bodyResult middle execution later extra extraBound
                have bodyBound := first bodyResult middle execution
                have lower := (evaluate_clock _ _ _ middle execution).1
                rw [entryClock] at bodyBound lower
                have syntaxBound : sizeOf retCode + wordHandlerSize handler <
                    sizeOf (.call (some (values,names,retCode,l1,l2)) dest args handler : WordLangProgHOL (BitVec width)) := by
                  cases handler with
                  | none => simp only [wordHandlerSize]; simp_wf; omega
                  | some h => rcases h with ⟨reg,hp,h1,h2⟩; simp only [wordHandlerSize]; simp_wf; omega
                have split : s.clock - post.clock =
                    1 + (s.clock - 1 - middle.clock) + (middle.clock - post.clock) := by omega
                rw [split, Nat.mul_add, Nat.mul_add, Nat.mul_one]
                omega
              split at run
              · rename_i x ys middle heq
                rw [fix_clock_evaluate] at heq
                have middleBound : WordCodeSize limit middle := by
                  have nb := entryBound.evaluated body selected.2
                  rwa [fix_clock_evaluate, heq] at nb
                have bodyLower := (evaluate_clock _ _ _ middle heq).1
                -- Facts about the actual post state and the reached continuation work.
                have postFacts : post.clock ≤ middle.clock ∧
                    ((x = .loc l1 l2 ∧ ys.length = values.length) →
                      ∀ popped, popEnv middle = some popped → sptDomainEqUnion popped.locals envs.1 envs.2 →
                        wordPathWork retCode (setVars values ys popped) ≤
                          (2 * limit + 2) * (middle.clock - post.clock) + 2 * sizeOf retCode) := by
                  by_cases mismatch : x ≠ .loc l1 l2 ∨ ys.length ≠ values.length
                  · rw [if_pos mismatch] at run
                    obtain ⟨-, rfl⟩ := Prod.mk.inj run
                    refine ⟨Nat.le_refl _, ?_⟩
                    intro valid
                    exact absurd (by omega) (by simpa [valid.1] using mismatch)
                  · rw [if_neg mismatch] at run
                    split at run
                    · obtain ⟨-, rfl⟩ := Prod.mk.inj run
                      refine ⟨Nat.le_refl _, ?_⟩
                      intro _ popped pop
                      rename_i none
                      simp_all
                    · rename_i popped pop
                      have popClock := popEnv_clock _ _ pop
                      by_cases domains : sptDomainEqUnion popped.locals envs.1 envs.2
                      · rw [if_pos domains] at run
                        have setClock : (setVars values ys popped).clock = middle.clock := by
                          simp only [setVars]; omega
                        have continuation := ih retCode (setVars values ys popped)
                          (workRank_clock _ _ _ _ _ (by omega) retSmall)
                          retSmall ((middleBound.popEnv pop).setVars values ys) retSafe result post run
                        have contClock := (evaluate_clock _ _ result post run).1
                        rw [setClock] at continuation contClock
                        refine ⟨contClock, ?_⟩
                        intro _ popped' pop' _
                        rw [pop] at pop'
                        cases pop'
                        exact continuation
                      · rw [if_neg domains] at run
                        obtain ⟨-, rfl⟩ := Prod.mk.inj run
                        refine ⟨by omega, ?_⟩
                        intro _ popped' pop' domains'
                        rw [pop] at pop'
                        cases pop'
                        exact absurd domains' domains
                split
                · rename_i location returned middle' execution
                  rw [fix_clock_evaluate, heq] at execution
                  simp only [Prod.mk.injEq, Option.some.injEq, WordSemResult.result.injEq] at execution
                  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := execution
                  by_cases mismatch : x ≠ .loc l1 l2 ∨ ys.length ≠ values.length
                  · rw [if_pos mismatch]
                    exact finish _ _ heq postFacts.1 0 (Nat.zero_le _)
                  · rw [if_neg mismatch]
                    have valid : x = .loc l1 l2 ∧ ys.length = values.length := by
                      constructor
                      · by_contra h; exact mismatch (Or.inl h)
                      · by_contra h; exact mismatch (Or.inr h)
                    split
                    · exact finish _ _ heq postFacts.1 0 (Nat.zero_le _)
                    · rename_i popped pop
                      by_cases domains : sptDomainEqUnion popped.locals envs.1 envs.2
                      · rw [if_pos domains]
                        exact finish _ _ heq postFacts.1 _
                          (Nat.le_trans (postFacts.2 valid popped pop domains) (by omega))
                      · rw [if_neg domains]
                        exact finish _ _ heq postFacts.1 0 (Nat.zero_le _)
                · rename_i location value middle' execution
                  rw [fix_clock_evaluate, heq] at execution
                  simp at execution
                · exact finish _ _ heq postFacts.1 0 (Nat.zero_le _)
              · rename_i x y middle heq
                rw [fix_clock_evaluate] at heq
                have middleBound : WordCodeSize limit middle := by
                  have nb := entryBound.evaluated body selected.2
                  rwa [fix_clock_evaluate, heq] at nb
                have bodyLower := (evaluate_clock _ _ _ middle heq).1
                split
                · rename_i location returned middle' execution
                  rw [fix_clock_evaluate, heq] at execution
                  simp at execution
                · rename_i location value middle' execution
                  rw [fix_clock_evaluate, heq] at execution
                  simp only [Prod.mk.injEq, Option.some.injEq, WordSemResult.exception.injEq] at execution
                  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := execution
                  cases handler with
                  | none =>
                    simp only at run ⊢
                    obtain ⟨-, rfl⟩ := Prod.mk.inj run
                    exact finish _ _ heq (Nat.le_refl _) 0 (Nat.zero_le _)
                  | some h =>
                    rcases h with ⟨reg,hp,h1,h2⟩
                    have handlerSize : sizeOf hp < sizeOf (.call (some (values,names,retCode,l1,l2)) dest args
                        (some (reg,hp,h1,h2)) : WordLangProgHOL (BitVec width)) := by simp_wf; omega
                    have handlerSafe := noInstall_call_handler safe
                    simp only at run ⊢
                    by_cases mismatch : x ≠ .loc h1 h2
                    · rw [if_pos mismatch]
                      rw [if_pos mismatch] at run
                      obtain ⟨-, rfl⟩ := Prod.mk.inj run
                      exact finish _ _ heq (Nat.le_refl _) 0 (Nat.zero_le _)
                    · rw [if_neg mismatch]
                      rw [if_neg mismatch] at run
                      by_cases domains : sptDomainEqUnion middle.locals envs.1 envs.2
                      · rw [if_pos domains]
                        rw [if_pos domains] at run
                        have continuation := ih hp (setVar reg y middle)
                          (workRank_clock _ _ _ _ _ (by simp only [setVar]; omega) (by omega))
                          (by omega) (middleBound.setVar reg y) handlerSafe result post run
                        have contClock := (evaluate_clock _ _ result post run).1
                        have setClock : (setVar reg y middle).clock = middle.clock := rfl
                        rw [setClock] at continuation contClock
                        exact finish _ _ heq contClock _ (by simp only [wordHandlerSize]; omega)
                      · rw [if_neg domains]
                        rw [if_neg domains] at run
                        obtain ⟨-, rfl⟩ := Prod.mk.inj run
                        exact finish _ _ heq (Nat.le_refl _) 0 (Nat.zero_le _)
                · have postLe : post.clock ≤ middle.clock := by
                    cases handler with
                    | none => simp only at run; rw [← (Prod.mk.inj run).2]
                    | some h =>
                      rcases h with ⟨reg,hp,h1,h2⟩
                      simp only at run
                      by_cases mismatch : x ≠ .loc h1 h2
                      · rw [if_pos mismatch] at run; rw [← (Prod.mk.inj run).2]
                      · rw [if_neg mismatch] at run
                        by_cases domains : sptDomainEqUnion middle.locals envs.1 envs.2
                        · rw [if_pos domains] at run; exact (evaluate_clock _ _ result post run).1
                        · rw [if_neg domains] at run; rw [← (Prod.mk.inj run).2]
                  exact finish _ _ heq postLe 0 (Nat.zero_le _)
              next s2 heq =>
                rw [fix_clock_evaluate] at heq
                obtain ⟨-, rfl⟩ := Prod.mk.inj run
                split
                · rename_i execution; rw [fix_clock_evaluate, heq] at execution; simp at execution
                · rename_i execution; rw [fix_clock_evaluate, heq] at execution; simp at execution
                · exact finish _ _ heq (Nat.le_refl _) 0 (Nat.zero_le _)
              next label s2 heq =>
                rw [fix_clock_evaluate] at heq
                obtain ⟨-, rfl⟩ := Prod.mk.inj run
                split
                · rename_i execution; rw [fix_clock_evaluate, heq] at execution; simp at execution
                · rename_i execution; rw [fix_clock_evaluate, heq] at execution; simp at execution
                · exact finish _ _ heq (Nat.le_refl _) 0 (Nat.zero_le _)
              next label s2 heq =>
                rw [fix_clock_evaluate] at heq
                obtain ⟨-, rfl⟩ := Prod.mk.inj run
                split
                · rename_i execution; rw [fix_clock_evaluate, heq] at execution; simp at execution
                · rename_i execution; rw [fix_clock_evaluate, heq] at execution; simp at execution
                · exact finish _ _ heq (Nat.le_refl _) 0 (Nat.zero_le _)
              · rename_i e1 e2 e3 e4 e5
                have heq := run
                rw [fix_clock_evaluate] at heq
                split
                · rename_i execution; exact (e1 _ _ _ execution).elim
                · rename_i execution; exact (e2 _ _ _ execution).elim
                · exact finish _ _ heq (Nat.le_refl _) 0 (Nat.zero_le _)

#print axioms wordPath_return_affine
end InitECandidate.Runtime.WordToStack
