import InitECandidate.Runtime.WordOptimizerPrice
import InitECandidate.Runtime.WordCostSupported
import Flapjack.Compiler.Backend.WordAlloc.Colour

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordAlloc
open InitECandidate.Runtime.WordToStack Flapjack.Compiler.Encoders.Asm

/-!
# Register colouring keeps the local Word price

`applyColour` renames registers only. Every refined Word-to-Stack leaf price
is a closed constant per constructor shape that already pays its worst-case
spill loads and stores, calls pay by arity, and the optimizer price charges a
parallel move per input pair. Colouring keeps all three, so the price is
preserved exactly, with coefficient one, for every colouring including
spilling ones (colours at least `2 * k`).
-/

theorem refinedNativeInstructionPrice_applyColourInst (f : Nat → Nat)
    (instruction : WordLangInst (BitVec 64)) :
    refinedNativeInstructionPrice (HolInst.ofWordLangInst (applyColourInst f instruction)) =
      refinedNativeInstructionPrice (HolInst.ofWordLangInst instruction) := by
  cases instruction with
  | skip | const _ _ => rfl
  | arith operation =>
    cases operation with
    | binop _ _ _ operand | shift _ _ _ operand => cases operand <;> rfl
    | _ => rfl
  | mem operator destination address =>
    cases address
    cases operator <;> rfl

/-- The intermediate optimizer price is invariant under every colouring. -/
theorem wordOptimizerLocalPrice_applyColour {C F : Type} (f : Nat → Nat)
    (p : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F) :
    wordOptimizerLocalPrice (applyColour f p) s = wordOptimizerLocalPrice p s := by
  cases p
  case call returns destination arguments handler =>
    rcases returns with _ | ⟨values, names, continuation, l1, l2⟩ <;>
      rcases handler with _ | ⟨reg, code, h1, h2⟩ <;>
      (rw [applyColour.eq_def]
       simp [wordOptimizerLocalPrice, refinedWordLocalPrice, refinedWordStackLeafBudget])
  all_goals simp [applyColour, wordOptimizerLocalPrice, refinedWordLocalPrice,
    refinedWordStackLeafBudget, refinedNativeInstructionPrice_applyColourInst]

/-- Colouring keeps the supported executed-cost syntax. -/
theorem wordCostSupported_applyColour (f : Nat → Nat) (p : WordLangProgHOL (BitVec 64)) :
    wordCostSupported (applyColour f p) = wordCostSupported p := by
  cases p
  case seq first second =>
    simp only [applyColour, wordCostSupported, wordCostSupported_applyColour f first,
      wordCostSupported_applyColour f second]
  case ite cmp reg operand first second =>
    simp only [applyColour, wordCostSupported, wordCostSupported_applyColour f first,
      wordCostSupported_applyColour f second]
  case loop names body exits =>
    simp only [applyColour, wordCostSupported, wordCostSupported_applyColour f body]
  case mustTerminate body =>
    simp only [applyColour, wordCostSupported, wordCostSupported_applyColour f body]
  case call returns destination arguments handler =>
    rcases returns with _ | ⟨values, names, continuation, l1, l2⟩ <;>
      rcases handler with _ | ⟨reg, code, h1, h2⟩
    · rw [applyColour.eq_def]; rfl
    · rw [applyColour.eq_def]
      simp only [wordCostSupported, wordCostSupported_applyColour f code]
    · rw [applyColour.eq_def]
      simp only [wordCostSupported, wordCostSupported_applyColour f continuation]
    · rw [applyColour.eq_def]
      simp only [wordCostSupported, wordCostSupported_applyColour f continuation,
        wordCostSupported_applyColour f code]
  all_goals simp [applyColour, wordCostSupported, refinedWordStackLeafBudget]
termination_by sizeOf p

#print axioms refinedNativeInstructionPrice_applyColourInst
#print axioms wordOptimizerLocalPrice_applyColour
#print axioms wordCostSupported_applyColour
end InitECandidate.Runtime.FineCost
