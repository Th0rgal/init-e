import InitECandidate.Runtime.WordWorkCeilingCalls
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.WordSemStateFiniteExact

theorem wordWork_return_ceiling {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F)
    (small : sizeOf (.call (some (values,names,retCode,l1,l2)) dest args handler : WordLangProgHOL (BitVec width)) ≤ limit)
    (bounded : WordCodeSize limit s)
    (safe : noInstallSubprogsHOL (.call (some (values,names,retCode,l1,l2)) dest args handler) = true)
    (ih : WordCeilingIH limit (.call (some (values,names,retCode,l1,l2)) dest args handler) s) :
    wordWork (.call (some (values,names,retCode,l1,l2)) dest args handler) s ≤
      workCeiling limit s.clock (sizeOf (.call (some (values,names,retCode,l1,l2)) dest args handler : WordLangProgHOL (BitVec width))) := by
  have unit : 1 ≤ workCeiling limit s.clock
      (sizeOf (.call (some (values,names,retCode,l1,l2)) dest args handler : WordLangProgHOL (BitVec width))) := by
    have h := two_le_workCeiling limit s.clock
      (sizeOf (.call (some (values,names,retCode,l1,l2)) dest args handler : WordLangProgHOL (BitVec width)))
    omega
  have retSmall : sizeOf retCode ≤ limit := by
    have smaller : sizeOf retCode < sizeOf (.call (some (values,names,retCode,l1,l2)) dest args handler : WordLangProgHOL (BitVec width)) := by simp_wf; omega
    omega
  have retSafe := noInstall_call_ret safe
  rw [wordWork]
  split
  · exact unit
  · rename_i xs vars
    by_cases bad : wordSemBadDestArgs dest args = true
    · rw [if_pos bad]
      exact unit
    · rw [if_neg bad]
      split
      · exact unit
      · rename_i foundArgs body ss found
        dsimp only
        by_cases invalid : sptDomainEmpty names.1 ∨ ¬values.Nodup
        · rw [if_pos invalid]
          exact unit
        · rw [if_neg invalid]
          split
          · exact unit
          · rename_i envs cut
            by_cases zero : s.clock = 0
            · rw [dif_pos zero]
              exact unit
            · rw [dif_neg zero]
              have selected := bounded.findCode dest (wordSemAddRetLoc (some (values,names,retCode,l1,l2)) xs) foundArgs body ss found
              let entry := callEnv foundArgs ss (pushEnv envs handler (decClock s))
              have strict : entry.clock < s.clock := by
                simp only [entry, Flapjack.WordSemStateFiniteExact.callEnv, pushEnv_clock, decClock]
                omega
              have entryBound : WordCodeSize limit entry :=
                (bounded.decClock.pushEnv envs handler).callEnv foundArgs ss
              have first := ih body entry (workRank_clock _ _ _ _ _ strict selected.1)
                selected.1 entryBound selected.2
              have nextBound := entryBound.evaluated body selected.2
              split
              · rename_i location returned middle execution
                have lower := (fixClock_IMP_LESS_EQ _ _ _ _ execution).1
                change middle.clock ≤ entry.clock at lower
                rw [execution] at nextBound
                by_cases mismatch : location ≠ .loc l1 l2 ∨ returned.length ≠ values.length
                · rw [if_pos mismatch]
                  change 1 + wordWork body entry + 0 ≤ _
                  exact Nat.le_trans (by omega) (workCeiling_one _ _ first)
                · rw [if_neg mismatch]
                  split
                  · change 1 + wordWork body entry + 0 ≤ _
                    exact Nat.le_trans (by omega) (workCeiling_one _ _ first)
                  · rename_i popped pop
                    by_cases domains : sptDomainEqUnion popped.locals envs.1 envs.2
                    · rw [if_pos domains]
                      have popClock := popEnv_clock _ _ pop
                      have continuation := ih retCode (setVars values returned popped)
                        (workRank_clock _ _ _ _ _ (by simp only [setVars]; omega) retSmall)
                        retSmall ((nextBound.popEnv pop).setVars values returned) retSafe
                      change 1 + wordWork body entry + wordWork retCode (setVars values returned popped) ≤ _
                      exact Nat.le_trans (by omega) (workCeiling_two _ _ _ first continuation)
                    · rw [if_neg domains]
                      change 1 + wordWork body entry + 0 ≤ _
                      exact Nat.le_trans (by omega) (workCeiling_one _ _ first)
              · rename_i location value middle execution
                have lower := (fixClock_IMP_LESS_EQ _ _ _ _ execution).1
                change middle.clock ≤ entry.clock at lower
                rw [execution] at nextBound
                cases handler with
                | none =>
                  change 1 + wordWork body entry + 0 ≤ _
                  exact Nat.le_trans (by omega) (workCeiling_one _ _ first)
                | some h =>
                  rcases h with ⟨reg,hp,h1,h2⟩
                  have handlerSmall : sizeOf hp ≤ limit := by
                    have smaller : sizeOf hp < sizeOf (.call (some (values,names,retCode,l1,l2)) dest args (some (reg,hp,h1,h2)) : WordLangProgHOL (BitVec width)) := by simp_wf; omega
                    omega
                  have handlerSafe := noInstall_call_handler safe
                  dsimp only
                  by_cases mismatch : location ≠ .loc h1 h2
                  · rw [if_pos mismatch]
                    change 1 + wordWork body entry + 0 ≤ _
                    exact Nat.le_trans (by omega) (workCeiling_one _ _ first)
                  · rw [if_neg mismatch]
                    by_cases domains : sptDomainEqUnion middle.locals envs.1 envs.2
                    · rw [if_pos domains]
                      have continuation := ih hp (setVar reg value middle)
                        (workRank_clock _ _ _ _ _ (by simp only [setVar]; omega) handlerSmall)
                        handlerSmall (nextBound.setVar reg value) handlerSafe
                      change 1 + wordWork body entry + wordWork hp (setVar reg value middle) ≤ _
                      exact Nat.le_trans (by omega) (workCeiling_two _ _ _ first continuation)
                    · rw [if_neg domains]
                      change 1 + wordWork body entry + 0 ≤ _
                      exact Nat.le_trans (by omega) (workCeiling_one _ _ first)
              · change 1 + wordWork body entry ≤ _
                exact Nat.le_trans (by omega) (workCeiling_one _ _ first)

#print axioms wordWork_return_ceiling
end InitECandidate.Runtime.WordToStack
