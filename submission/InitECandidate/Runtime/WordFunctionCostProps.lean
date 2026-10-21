import InitECandidate.Runtime.WordFunctionExecutionCost
import InitECandidate.Runtime.WordCseAtomicCost
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

/-- Pointwise price domination covers every executed function, including
indirect callees, without a program-size or call-depth multiplier. -/
theorem wordFunctionExecutionCost_mono {width : Nat} [NeZero width] {C F : Type}
    (small large : Nat → WordLangProgHOL (BitVec width) → WordSemStateFiniteExact width C F → Nat)
    (le : ∀ function program state, small function program state ≤ large function program state)
    (function : Nat) (program : WordLangProgHOL (BitVec width)) (source : WordSemStateFiniteExact width C F) :
    wordFunctionExecutionCost small function program source ≤ wordFunctionExecutionCost large function program source := by
  classical
  fun_induction wordFunctionExecutionCost small function program source <;>
    (try simp_all +zetaDelta [wordFunctionExecutionCost])
  all_goals grind (splits := 40) only

/-- A leaf has exactly its price at the current function identity. -/
theorem wordFunctionExecutionCost_atomic {C F : Type}
    (price : Nat → WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (function : Nat) (program : WordLangProgHOL (BitVec 64)) (source : WordSemStateFiniteExact 64 C F)
    (atomic : wordCostAtomic program = true) :
    wordFunctionExecutionCost price function program source = price function program source := by
  cases program <;> simp_all only [wordCostAtomic,Bool.false_eq_true,wordFunctionExecutionCost]

#print axioms wordFunctionExecutionCost_mono
#print axioms wordFunctionExecutionCost_atomic
end InitECandidate.Runtime.FineCost
