import InitECandidate.Runtime.WordWorkCeilingControl
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.WordSemStateFiniteExact

/-- Every continuing loop iteration consumes a clock before re-entry; cutting
locals and executing the body preserve the bounded no-install code invariant. -/
theorem wordWork_loop_ceiling {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (names exits : WordLangNumSetHOL) (body : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F)
    (small : sizeOf (.loop names body exits : WordLangProgHOL (BitVec width)) ≤ limit)
    (bounded : WordCodeSize limit s) (safe : noInstallSubprogsHOL (.loop names body exits) = true)
    (ih : WordCeilingIH limit (.loop names body exits) s) :
    wordWork (.loop names body exits) s ≤
      workCeiling limit s.clock (sizeOf (.loop names body exits : WordLangProgHOL (BitVec width))) := by
  have bodySize : sizeOf body < sizeOf (.loop names body exits : WordLangProgHOL (BitVec width)) := by
    simp_wf
    omega
  have bodySafe : noInstallSubprogsHOL body = true := by
    simpa [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] using safe
  rw [wordWork]
  split
  · have bound := two_le_workCeiling limit s.clock (sizeOf (.loop names body exits : WordLangProgHOL (BitVec width)))
    omega
  · rename_i cutSource cut
    have sameClock := (cutState_clock_termdep _ _ _ cut).1
    have cutBound := bounded.cutState _ cut
    have first := ih body cutSource (workRank_subprogram _ _ _ _ _ (by omega) bodySize)
      (by omega) cutBound bodySafe
    split
    rename_i result middle execution
    have lower := (fixClock_IMP_LESS_EQ _ _ _ _ execution).1
    have middleBound := cutBound.evaluated body bodySafe
    rw [execution] at middleBound
    split_ifs with continuing zero
    · change 1 + wordWork body cutSource + 0 ≤ _
      have bound := workCeiling_one _ _ first
      exact Nat.le_trans (by omega) bound
    · have strict : (decClock middle).clock < s.clock := by
        simp only [decClock]
        omega
      have next := ih (.loop names body exits) (decClock middle)
        (workRank_clock _ _ _ _ _ strict small) small middleBound.decClock safe
      change 1 + wordWork body cutSource + wordWork (.loop names body exits) (decClock middle) ≤ _
      exact Nat.le_trans (by omega) (workCeiling_two _ _ _ first next)
    · change 1 + wordWork body cutSource + 0 ≤ _
      have bound := workCeiling_one _ _ first
      exact Nat.le_trans (by omega) bound

#print axioms wordWork_loop_ceiling
end InitECandidate.Runtime.WordToStack
