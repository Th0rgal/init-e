import InitECandidate.Runtime.WordWorkCeilingLoop
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.WordSemStateFiniteExact

/-- A tail call spends one source clock before entering a bounded selected body. -/
theorem wordWork_tail_ceiling {width : Nat} [NeZero width] {C F : Type}
    (limit : Nat) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F) (bounded : WordCodeSize limit s)
    (ih : WordCeilingIH limit (.call none dest args handler) s) :
    wordWork (.call none dest args handler) s ≤
      workCeiling limit s.clock (sizeOf (.call none dest args handler : WordLangProgHOL (BitVec width))) := by
  have unit : 1 ≤ workCeiling limit s.clock
      (sizeOf (.call none dest args handler : WordLangProgHOL (BitVec width))) := by
    have h := two_le_workCeiling limit s.clock
      (sizeOf (.call none dest args handler : WordLangProgHOL (BitVec width)))
    omega
  rw [wordWork]
  split
  · exact unit
  · rename_i values vars
    by_cases bad : wordSemBadDestArgs dest args = true
    · rw [if_pos bad]
      exact unit
    · rw [if_neg bad]
      split
      · exact unit
      · rename_i foundArgs body ss found
        dsimp only
        cases handler with
        | some handler => exact unit
        | none =>
          dsimp only
          split_ifs with zero
          · exact unit
          · have selected := bounded.findCode dest values foundArgs body ss found
            have strict : (callEnv foundArgs ss (decClock s)).clock < s.clock := by
              simp only [Flapjack.WordSemStateFiniteExact.callEnv, decClock]
              omega
            have child := ih body (callEnv foundArgs ss (decClock s))
              (workRank_clock _ _ _ _ _ strict selected.1) selected.1
              (bounded.decClock.callEnv foundArgs ss) selected.2
            exact Nat.le_trans (by omega) (workCeiling_one _ _ child)

#print axioms wordWork_tail_ceiling
end InitECandidate.Runtime.WordToStack
