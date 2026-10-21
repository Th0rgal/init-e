import InitECandidate.Runtime.WordOptimizerPrice
import Flapjack.Compiler.Backend.WordCse.Transform

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend
open InitECandidate.Runtime.WordToStack

/-- A CSE hit emits one move; a miss retains the original instruction. The
24 floor pays for the hit even when the retained instruction was cheaper. -/
theorem cse_addToDataAux_price_le {C F : Type}
    (data : WordCse.Knowledge) (destination : Nat) (key : List Nat)
    (original : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F)
    (floor : 24 ≤ wordOptimizerLocalPrice original source) :
    wordOptimizerLocalPrice (WordCse.addToDataAux data destination key original).2 target ≤
      wordOptimizerLocalPrice original source := by
  unfold WordCse.addToDataAux
  split
  · split <;> simpa [wordOptimizerLocalPrice] using floor
  · split <;> exact le_of_eq (wordOptimizerLocalPrice_state_independent original target source)

theorem cse_addToLoadAux_price_le {C F : Type}
    (data : WordCse.Knowledge) (destination : Nat) (key : List Nat)
    (original : WordLangProgHOL (BitVec 64))
    (source target : WordSemStateFiniteExact 64 C F)
    (floor : 24 ≤ wordOptimizerLocalPrice original source) :
    wordOptimizerLocalPrice (WordCse.addToLoadAux data destination key original).2 target ≤
      wordOptimizerLocalPrice original source := by
  unfold WordCse.addToLoadAux
  split
  · split <;> simpa [wordOptimizerLocalPrice] using floor
  · split <;> exact le_of_eq (wordOptimizerLocalPrice_state_independent original target source)

/-- Every branch of the pinned Get clause pays no more than the intermediate
Get price, including hits that become a singleton parallel assignment. -/
theorem cse_getClause_price_le {C F : Type}
    (data : WordCse.Knowledge) (destination : Nat) (store : WordStoreHOL)
    (source target : WordSemStateFiniteExact 64 C F) :
    wordOptimizerLocalPrice (WordCse.getClause (width := 64) data destination store).2 target ≤
      wordOptimizerLocalPrice (.get destination store) source := by
  cases found : (WordCse.invalidateData data destination).getsMem.lookup store <;>
    by_cases even : destination % 2 = 0 <;>
    simp [WordCse.getClause, found, even, wordOptimizerLocalPrice,
      refinedWordLocalPrice, refinedWordStackLeafBudget]

/-- CSE's complete instruction transformer either retains the input or
replaces it by one move. Its local executed price is nonincreasing under the
shared intermediate price, without any knowledge-validity assumption. The
semantic relation is a separate obligation of the whole pass. -/
theorem cse_instruction_price_le {C F : Type}
    (data : WordCse.Knowledge) (instruction : Compiler.Encoders.Asm.HolInst 64)
    (source target : WordSemStateFiniteExact 64 C F) :
    wordOptimizerLocalPrice (WordCse.wordCseInst data instruction).2 target ≤
      wordOptimizerLocalPrice (.inst instruction.toWordLangInst) source := by
  cases instruction with
  | skip => exact le_of_eq (wordOptimizerLocalPrice_state_independent _ target source)
  | const destination value =>
    dsimp only [WordCse.wordCseInst]
    split
    · exact le_of_eq (wordOptimizerLocalPrice_state_independent _ target source)
    · dsimp only [WordCse.addToDataConst]
      split <;> exact le_of_eq (wordOptimizerLocalPrice_state_independent _ target source)
  | arith operation =>
    dsimp only [WordCse.wordCseInst]
    split
    · unfold WordCse.addToData
      apply cse_addToDataAux_price_le
      simp [wordOptimizerLocalPrice]
    · exact le_of_eq (wordOptimizerLocalPrice_state_independent _ target source)
  | mem operation destination address =>
    cases address
    dsimp only [WordCse.wordCseInst]
    split
    · exact le_of_eq (wordOptimizerLocalPrice_state_independent _ target source)
    · split
      · exact le_of_eq (wordOptimizerLocalPrice_state_independent _ target source)
      · apply cse_addToLoadAux_price_le
        simp [wordOptimizerLocalPrice]

#print axioms cse_instruction_price_le
#print axioms cse_addToDataAux_price_le
#print axioms cse_addToLoadAux_price_le
#print axioms cse_getClause_price_le
end InitECandidate.Runtime.FineCost
