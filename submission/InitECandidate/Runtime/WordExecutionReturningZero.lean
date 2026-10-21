import InitECandidate.Runtime.WordExecutionReturningCost
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact

/-- A zero-clock returning call executes no callee or continuation. -/
theorem wordExecutionCost_returning_zero {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 (Nat × C) F → Nat)
    (values : List Nat) (names : WordLangCutsetsHOL)
    (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (source : WordSemStateFiniteExact 64 (Nat × C) F)
    (xs args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64))
    (ss : Option Nat) (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (guards : Flapjack.WordToStackProofs.CompCorrect.CallReturning.SourceGuards
      values names retCode l1 l2 dest args source xs args1 prog ss envs)
    (zero : source.clock = 0) :
    wordExecutionCost price (.call (some (values,names,retCode,l1,l2)) dest args handler) source =
      price (.call (some (values,names,retCode,l1,l2)) dest args handler) source := by
  rcases guards with ⟨get,bad,find,valid,cut⟩
  rw [wordExecutionCost]
  simp only [get,bad,Bool.false_eq_true,↓reduceIte,find,valid,cut,zero,dite_true]

#print axioms wordExecutionCost_returning_zero
end InitECandidate.Runtime.FineCost
