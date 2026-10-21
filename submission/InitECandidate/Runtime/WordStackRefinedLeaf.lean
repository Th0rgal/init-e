import InitECandidate.Runtime.WordStackRefinedSimulation
import InitECandidate.Runtime.WordStackExecutedRaise
import InitECandidate.Runtime.WordExecutionCostLowerBound
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Runtime.FineCost

/-- Closed compiler-fragment prices for supported leaves. No target-run
budget is supplied; each entry is justified by its lowering proof below. -/
def refinedWordStackLeafBudget : WordLangProgHOL (BitVec 64) → Option Nat
  | .skip | .continue _ | .mustTerminate _ => some 0
  | .tick => some 6
  | .break _ => some 2
  | .inst i => some (refinedNativeInstructionPrice (HolInst.ofWordLangInst i))
  | .move _ [_] => some 12
  | .move _ moves => some (24*moves.length)
  | .get _ _ | .set _ _ => some 12
  | .locValue _ _ => some 14
  | .return _ _ => some 15
  | .opCurrHeap _ _ _ => some 18
  | .ffi _ _ _ _ _ _ => some 25
  | .raise _ => some 63
  | _ => none

theorem refinedExecutedSimulation_leaf {F : Type} (ac : AsmConfigExact 64)
    (program : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (budget : Nat) (priced : refinedWordStackLeafBudget program = some budget) :
    RefinedExecutedSimulation ac program source budget := by
  cases program <;> simp only [refinedWordStackLeafBudget,Option.some.injEq,reduceCtorEq] at priced
  case skip => subst budget; exact refinedExecutedSimulation_skip ac source
  case tick => subst budget; exact refinedExecutedSimulation_tick ac source
  case inst instruction => subst budget; exact refinedExecutedSimulation_native_instruction ac instruction source
  case move priority moves =>
    cases moves with
    | nil =>
      simp only [refinedWordStackLeafBudget,Option.some.injEq] at priced
      subst budget
      exact refinedExecutedSimulation_move ac priority [] source
    | cons pair rest =>
      cases rest with
      | nil =>
        simp only [refinedWordStackLeafBudget,Option.some.injEq] at priced
        subst budget
        exact refinedExecutedSimulation_singleton_move ac priority pair.1 pair.2 source
      | cons next rest =>
        simp only [refinedWordStackLeafBudget,Option.some.injEq] at priced
        subst budget
        exact refinedExecutedSimulation_move ac priority (pair::next::rest) source
  case get register name => subst budget; exact refinedExecutedSimulation_get ac register name source
  case set name expression => subst budget; exact refinedExecutedSimulation_set ac name expression source
  case locValue register location => subst budget; exact refinedExecutedSimulation_locValue ac register location source
  case «return» register names => subst budget; exact executedSimulation_to_refined (executedSimulation_return ac register names source)
  case opCurrHeap operator dst src => subst budget; exact refinedExecutedSimulation_opCurrHeap ac operator dst src source
  case ffi index ptr1 len1 ptr2 len2 names => subst budget; exact refinedExecutedSimulation_ffi ac index ptr1 len1 ptr2 len2 names source
  case «raise» name => subst budget; exact executedSimulation_to_refined (executedSimulation_raise ac name source)
  case «break» label => subst budget; exact refinedExecutedSimulation_break ac label source
  case «continue» label => subst budget; exact refinedExecutedSimulation_continue ac label source
  case mustTerminate body => subst budget; exact refinedExecutedSimulation_mustTerminate ac body source

/-- Refinement leaves compose with the same source-cost coefficient. -/
theorem refinedExecutedSimulation_fine_leaf {F : Type} (ac : AsmConfigExact 64)
    (price : WordLangProgHOL (BitVec 64) →
      WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F → Nat)
    (factor : Nat) (program : WordLangProgHOL (BitVec 64))
    (source : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (budget : Nat) (priced : refinedWordStackLeafBudget program = some budget)
    (localBound : budget ≤ factor * price program source) :
    RefinedExecutedSimulation ac program source (factor * wordExecutionCost price program source) :=
  (refinedExecutedSimulation_leaf ac program source budget priced).mono
    (localBound.trans (Nat.mul_le_mul_left factor (wordExecutionCost_local_le price program source)))

#print axioms refinedExecutedSimulation_leaf
#print axioms refinedExecutedSimulation_fine_leaf
end InitECandidate.Runtime.WordToStack
