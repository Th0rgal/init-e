import InitECandidate.Runtime.WordStackExecutedStore
import InitECandidate.Runtime.WordStackExecutedRaise
import InitECandidate.Runtime.WordExecutionCostLowerBound
import InitECandidate.Runtime.WordStackMoveCost
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Runtime.FineCost

/-- Only implemented primitive compiler clauses have a local bound here.
Variable-size move/bulk operations and recursive calls need their own proofs. -/
def wordStackLeafBudget : WordLangProgHOL (BitVec 64) → Option Nat
  | .skip | .continue _ | .mustTerminate _ => some 0
  | .tick => some 7
  | .break _ => some 2
  | .inst _ => some 43
  | .move _ moves => some (28 * moves.length)
  | .get _ _ | .set _ _ => some 14
  | .locValue _ _ | .return _ _ => some 15
  | .opCurrHeap _ _ _ => some 21
  | .ffi _ _ _ _ _ _ => some 25
  | .raise _ => some 63
  | _ => none

theorem executedSimulation_leaf {F : Type} (ac : AsmConfigExact 64)
    (p : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (budget : Nat) (priced : wordStackLeafBudget p = some budget) :
    ExecutedSimulation ac p source budget := by
  cases p <;> simp only [wordStackLeafBudget, Option.some.injEq, reduceCtorEq] at priced
  all_goals subst budget
  case skip => exact executedSimulation_skip ac source
  case tick => exact executedSimulation_tick ac source
  case inst instruction => exact executedSimulation_inst ac instruction source
  case move priority moves => exact executedSimulation_move ac priority moves source
  case get register name => exact executedSimulation_get ac register name source
  case set name expression => exact executedSimulation_set ac name expression source
  case locValue register location => exact executedSimulation_locValue ac register location source
  case «return» register names => exact executedSimulation_return ac register names source
  case opCurrHeap operator dst src => exact executedSimulation_opCurrHeap ac operator dst src source
  case ffi index ptr1 len1 ptr2 len2 names => exact executedSimulation_ffi ac index ptr1 len1 ptr2 len2 names source
  case «raise» name => exact executedSimulation_raise ac name source
  case «break» label => exact executedSimulation_break ac label source
  case «continue» label => exact executedSimulation_continue ac label source
  case mustTerminate body => exact executedSimulation_mustTerminate ac body source

/-- A proved primitive price lifts to the actual fine executed source
counter. This introduces no factor for enclosing syntax or call depth. -/
theorem executedSimulation_fine_leaf {F : Type} (ac : AsmConfigExact 64)
    (price : WordLangProgHOL (BitVec 64) →
      WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F → Nat)
    (factor : Nat) (p : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (budget : Nat) (priced : wordStackLeafBudget p = some budget)
    (localBound : budget ≤ factor * price p source) :
    ExecutedSimulation ac p source (factor * wordExecutionCost price p source) :=
  (executedSimulation_leaf ac p source budget priced).mono
    (localBound.trans (Nat.mul_le_mul_left factor (wordExecutionCost_local_le price p source)))

#print axioms executedSimulation_leaf
#print axioms executedSimulation_fine_leaf
end InitECandidate.Runtime.WordToStack
