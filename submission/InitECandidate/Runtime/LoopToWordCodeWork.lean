import InitECandidate.Runtime.LoopToWordExpressionWork
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopToWord

/-- Word work for the nonrecursive expression-generated subset. The lowered
conditional tick is explicit. Unsupported calls/loops are never given zero cost. -/
def wordExpressionCodeWork : WordLangProgHOL (BitVec 64) → Option Nat
  | .skip => some 0
  | .assign _ value => some (1 + wordExpressionWork value)
  | .inst _ | .tick => some 1
  | .seq first second => do
      let a ← wordExpressionCodeWork first
      let b ← wordExpressionCodeWork second
      pure (a+b)
  | .ite _ _ _ yes no => do
      let a ← wordExpressionCodeWork yes
      let b ← wordExpressionCodeWork no
      pure (1 + max a b)
  | _ => none
termination_by p => sizeOf p

/-- Loop-to-Word preserves the locally calibrated expression-code allowance.
This is a generated-work theorem; the later native instruction expansion remains
separate from the semantic source/target value correspondence. -/
theorem loop_to_word_code_work (context : Spt Nat) (p : HolLoopProg 64)
    (labels : Nat × Nat) (cost : Nat)
    (supported : loopExpressionCodeWork p = some cost) :
    wordExpressionCodeWork (LoopToWord.compHOL context p labels).1 = some cost := by
  cases p with
  | skip => simpa [loopExpressionCodeWork, wordExpressionCodeWork, LoopToWord.compHOL] using supported
  | assign name expression =>
    simpa [loopExpressionCodeWork, wordExpressionCodeWork, LoopToWord.compHOL, loop_to_word_expression_work] using supported
  | arith operation =>
    cases operation <;> simpa [loopExpressionCodeWork, wordExpressionCodeWork, LoopToWord.compHOL] using supported
  | load32 address destination => simpa [loopExpressionCodeWork, wordExpressionCodeWork, LoopToWord.compHOL] using supported
  | loadByte address destination => simpa [loopExpressionCodeWork, wordExpressionCodeWork, LoopToWord.compHOL] using supported
  | seq first second =>
    cases ha : loopExpressionCodeWork first <;> cases hb : loopExpressionCodeWork second <;>
      simp [loopExpressionCodeWork, ha, hb] at supported
    rename_i a b
    rcases ca : LoopToWord.compHOL context first labels with ⟨wordFirst, next⟩
    rcases cb : LoopToWord.compHOL context second next with ⟨wordSecond, final⟩
    have wa := loop_to_word_code_work context first labels a ha
    have wb := loop_to_word_code_work context second next b hb
    rw [ca] at wa
    rw [cb] at wb
    simpa [LoopToWord.compHOL, ca, cb, wordExpressionCodeWork, wa, wb] using supported
  | ite operator register right yes no live =>
    cases ha : loopExpressionCodeWork yes <;> cases hb : loopExpressionCodeWork no <;>
      simp [loopExpressionCodeWork, ha, hb] at supported
    rename_i a b
    rcases ca : LoopToWord.compHOL context yes labels with ⟨wordYes, next⟩
    rcases cb : LoopToWord.compHOL context no next with ⟨wordNo, final⟩
    have wa := loop_to_word_code_work context yes labels a ha
    have wb := loop_to_word_code_work context no next b hb
    rw [ca] at wa
    rw [cb] at wb
    rw [LoopToWord.compHOL.eq_def]
    dsimp only
    rw [ca]
    dsimp only
    rw [cb]
    simpa [wordExpressionCodeWork, wa, wb, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using supported
  | _ => simp [loopExpressionCodeWork] at supported
termination_by sizeOf p

#print axioms loop_to_word_code_work
end InitECandidate.Runtime.FineCost
