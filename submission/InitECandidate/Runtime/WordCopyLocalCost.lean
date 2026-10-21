import InitECandidate.Runtime.WordOptimizerPrice
import Flapjack.Compiler.Backend.WordCopy

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Runtime.WordToStack

/-- Copy propagation retains parallel assignment length, regardless of its
alias knowledge. This counts input pairs, not an assumed scheduler invariant. -/
theorem copyPropMove_pairs_length (moves : List (Nat × Nat)) (aliases : WordCopy.CopyState) :
    (WordCopy.copyPropMove moves aliases).1.length = moves.length := by
  induction moves with
  | nil => simp [WordCopy.copyPropMove]
  | cons head tail ih =>
    rcases head with ⟨destination, source⟩
    simp [WordCopy.copyPropMove, ih]

/-- The pinned copy-propagation instruction clauses preserve the native
instruction price. Register aliases never change immediate/register shape. -/
theorem copyPropInst_price_le {C F : Type}
    (instruction : WordLangInst (BitVec 64)) (aliases : WordCopy.CopyState)
    (source target : WordSemStateFiniteExact 64 C F) :
    wordOptimizerLocalPrice (WordCopy.copyPropInst instruction aliases).1 target ≤
      wordOptimizerLocalPrice (.inst instruction) source := by
  cases instruction with
  | skip => simp [WordCopy.copyPropInst, wordOptimizerLocalPrice,
      refinedWordLocalPrice, refinedWordStackLeafBudget, refinedNativeInstructionPrice,
      Compiler.Encoders.Asm.HolInst.ofWordLangInst]
  | const destination value =>
    exact le_of_eq (wordOptimizerLocalPrice_state_independent _ target source)
  | arith operation =>
    cases operation with
    | binop operator destination left operand | shift operator destination left operand =>
      cases operand <;> simp only [WordCopy.copyPropInst, WordCopy.lookupEqImm] <;>
        (try split_ifs) <;>
        simp_all [wordOptimizerLocalPrice, refinedWordLocalPrice, refinedWordStackLeafBudget,
          refinedNativeInstructionPrice, Compiler.Encoders.Asm.HolInst.ofWordLangInst,
          Compiler.Encoders.Asm.HolArith.ofWordLangArith,
          Compiler.Encoders.Asm.HolRegImm.ofWordRegImm]
    | _ =>
      simp only [WordCopy.copyPropInst, WordCopy.lookupEqImm]
      (try split_ifs) <;>
        simp_all [wordOptimizerLocalPrice, refinedWordLocalPrice, refinedWordStackLeafBudget,
          refinedNativeInstructionPrice, Compiler.Encoders.Asm.HolInst.ofWordLangInst,
          Compiler.Encoders.Asm.HolArith.ofWordLangArith,
          Compiler.Encoders.Asm.HolRegImm.ofWordRegImm]
  | mem operation destination address =>
    cases address
    cases operation <;>
      simp [WordCopy.copyPropInst, wordOptimizerLocalPrice, refinedWordLocalPrice,
        refinedWordStackLeafBudget, refinedNativeInstructionPrice,
        Compiler.Encoders.Asm.HolInst.ofWordLangInst]

#print axioms copyPropMove_pairs_length
#print axioms copyPropInst_price_le
end InitECandidate.Runtime.FineCost
