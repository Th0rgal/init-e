import InitECandidate.Runtime.WordExecutionCostProps
import InitECandidate.Runtime.SourceCostLoopWork
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact

/-! The Word price of the Loop-to-Word transfer. Every node pays a small local
price of its own syntax; structural nodes are free; `Tick` pays its native
`Skip`. An assignment pays its expression work, whose root node is the move
itself. A call pays one word per argument, and a returning call pays its return
names exactly when its callee body returns a value of that length (the native
return suffix runs only then): the price is state dependent. -/

/-- The callee body of a returning call returns a value list of the call's
return arity. -/
def wordCallReturned {C F : Type} (p : WordLangProgHOL (BitVec 64))
    (s : WordSemStateFiniteExact 64 C F) : Prop :=
  match p with
  | .call (some (rets, cutset, retCode, l1, l2)) dest args handler =>
      s.clock ≠ 0 ∧ ∃ xs args1 prog ss envs loc vals m,
        getVars args s = some xs ∧
        wordSemFindCode dest (wordSemAddRetLoc (some (rets, cutset, retCode, l1, l2)) xs) s.code
          s.stackSize = some (args1, prog, ss) ∧
        wordSemCutEnvs cutset s.locals = some envs ∧
        evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s))) =
          (some (.result loc vals), m) ∧
        vals.length = rets.length
  | _ => False

open Classical in
noncomputable def loopWordPrice {C F : Type} (p : WordLangProgHOL (BitVec 64))
    (s : WordSemStateFiniteExact 64 C F) : Nat :=
  match p with
  | .skip | .seq _ _ | .mustTerminate _ => 0
  | .assign _ value => wordExpressionWork value
  | .set _ value | .store value _ | .shareInst _ _ value => 1 + wordExpressionWork value
  | .move _ moves => 1 + moves.length
  | .storeConsts _ _ _ _ words => 1 + words.length
  | .return _ values => 1 + values.length
  | .call none _ arguments _ => arguments.length
  | .call (some (returns, _)) _ arguments _ =>
      arguments.length + if wordCallReturned p s then returns.length else 0
  | _ => 1

section leaves
variable {C F : Type} (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
  (s : WordSemStateFiniteExact 64 C F)
theorem wordCost_skip : wordExecutionCost price .skip s = price .skip s := by rw [wordExecutionCost] <;> simp
theorem wordCost_tick : wordExecutionCost price .tick s = price .tick s := by rw [wordExecutionCost] <;> simp
theorem wordCost_assign (n e) : wordExecutionCost price (.assign n e) s = price (.assign n e) s := by
  rw [wordExecutionCost] <;> simp
theorem wordCost_set (n e) : wordExecutionCost price (.set n e) s = price (.set n e) s := by
  rw [wordExecutionCost] <;> simp
theorem wordCost_store (e n) : wordExecutionCost price (.store e n) s = price (.store e n) s := by
  rw [wordExecutionCost] <;> simp
theorem wordCost_inst (i) : wordExecutionCost price (.inst i) s = price (.inst i) s := by
  rw [wordExecutionCost] <;> simp
theorem wordCost_break (k) : wordExecutionCost price (.break k) s = price (.break k) s := by
  rw [wordExecutionCost] <;> simp
theorem wordCost_continue (k) : wordExecutionCost price (.continue k) s = price (.continue k) s := by
  rw [wordExecutionCost] <;> simp
theorem wordCost_raise (n) : wordExecutionCost price (.raise n) s = price (.raise n) s := by
  rw [wordExecutionCost] <;> simp
theorem wordCost_return (n ms) : wordExecutionCost price (.return n ms) s = price (.return n ms) s := by
  rw [wordExecutionCost] <;> simp
theorem wordCost_locValue (r l) : wordExecutionCost price (.locValue r l) s = price (.locValue r l) s := by
  rw [wordExecutionCost] <;> simp
theorem wordCost_ffi (i a b c d n) :
    wordExecutionCost price (.ffi i a b c d n) s = price (.ffi i a b c d n) s := by
  rw [wordExecutionCost] <;> simp
theorem wordCost_shareInst (o v e) :
    wordExecutionCost price (.shareInst o v e) s = price (.shareInst o v e) s := by
  rw [wordExecutionCost] <;> simp

/-- Sequencing costs at most the first part plus a state-independent bound on
the second. -/
theorem wordCost_seq_le (a b : WordLangProgHOL (BitVec 64)) (bound : Nat)
    (second : ∀ m, wordExecutionCost price b m ≤ bound) :
    wordExecutionCost price (.seq a b) s ≤ price (.seq a b) s + wordExecutionCost price a s + bound := by
  rw [wordExecutionCost_seq]
  split
  · rename_i middle _; have := second middle; omega
  · omega
end leaves

attribute [local simp] wordCost_skip wordCost_tick wordCost_assign wordCost_set wordCost_store wordCost_inst
  wordCost_break wordCost_continue wordCost_raise wordCost_return wordCost_locValue wordCost_ffi
  wordCost_shareInst

/-- Compiled non-recursive Loop statements cost at most their `LoopWork`
leaf price, from every Word state. -/
theorem loop_word_leaf {C F : Type} (context : Spt Nat) (p : HolLoopProg 64) (labels : Nat × Nat)
    (cost : Nat) (leaf : loopWorkLeafCost p = some cost) (t : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost loopWordPrice (LoopToWord.compHOL context p labels).1 t ≤ cost := by
  cases p with
  | primitive destinations operation arguments =>
    simp only [loopWorkLeafCost, Option.some.injEq] at leaf
    subst leaf
    cases operation
    unfold LoopToWord.compHOL
    split
    · rename_i result carry left right carryIn
      have last : ∀ m : WordSemStateFiniteExact 64 C F, wordExecutionCost loopWordPrice
          (.seq (.assign (LoopToWord.findVarHOL context carry) (.var 1))
            (.assign (LoopToWord.findVarHOL context result) (.var 3))) m ≤ 2 := fun m =>
        Nat.le_trans (wordCost_seq_le _ _ _ _ 1 fun _ => by simp [loopWordPrice, wordExpressionWork])
          (by simp [loopWordPrice, wordExpressionWork])
      have middle : ∀ m : WordSemStateFiniteExact 64 C F, wordExecutionCost loopWordPrice
          (.seq (.inst (.arith (.addCarry 3 (LoopToWord.findVarHOL context left)
              (LoopToWord.findVarHOL context right) 1)))
            (.seq (.assign (LoopToWord.findVarHOL context carry) (.var 1))
              (.assign (LoopToWord.findVarHOL context result) (.var 3)))) m ≤ 3 := fun m =>
        Nat.le_trans (wordCost_seq_le _ _ _ _ 2 last) (by simp [loopWordPrice])
      refine Nat.le_trans (wordCost_seq_le _ _ _ _ 3 middle) ?_
      simp [loopWordPrice, wordExpressionWork]
    · simp [loopWordPrice]
  | arith operation =>
    simp only [loopWorkLeafCost, Option.some.injEq] at leaf
    subst leaf
    cases operation <;> simp [LoopToWord.compHOL, loopWordPrice]
  | assign name value =>
    simp only [loopWorkLeafCost, Option.some.injEq] at leaf
    subst leaf
    simp [LoopToWord.compHOL, loopWordPrice, loop_to_word_expression_work]
  | store value address =>
    simp only [loopWorkLeafCost, Option.some.injEq] at leaf
    subst leaf
    simp [LoopToWord.compHOL, loopWordPrice, loop_to_word_expression_work]
  | setGlobal address value =>
    simp only [loopWorkLeafCost, Option.some.injEq] at leaf
    subst leaf
    simp [LoopToWord.compHOL, loopWordPrice, loop_to_word_expression_work]
  | shMem operation name value =>
    simp only [loopWorkLeafCost, Option.some.injEq] at leaf
    subst leaf
    simp [LoopToWord.compHOL, loopWordPrice, loop_to_word_expression_work]
  | «return» values =>
    simp only [loopWorkLeafCost, Option.some.injEq] at leaf
    subst leaf
    simp [LoopToWord.compHOL, loopWordPrice]
  | seq _ _ | ite _ _ _ _ _ _ | loop _ _ _ | mark _ | call _ _ _ _ => simp [loopWorkLeafCost] at leaf
  | _ =>
    simp only [loopWorkLeafCost, Option.some.injEq] at leaf
    subst leaf
    simp [LoopToWord.compHOL, loopWordPrice]

#print axioms wordCost_seq_le
#print axioms loop_word_leaf
end InitECandidate.Runtime.FineCost
