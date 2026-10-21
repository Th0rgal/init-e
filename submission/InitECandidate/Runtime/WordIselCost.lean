import InitECandidate.Runtime.WordOptimizerPrice
import InitECandidate.Runtime.WordLineCost
import Flapjack.Compiler.Backend.WordInst.ExecutableInstSelect

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend

/-! Pre-allocation Word prices and the instruction-selection cost bound.

Between instruction selection and register allocation, move lists are renamed,
merged and deleted by the pinned passes, so a move is priced by its raw pair
count (`rawMovePrice`: 24 per pair, as in the shared optimizer price). Every other
leaf keeps its canonical `refinedWordStackLeafBudget`, with a floor of 24 on
the heads that copy propagation and CSE may replace by a single move
(instructions, `get`, `locValue`, `opCurrHeap`). Instruction selection
turns an expression into straight-line code whose static cost under these
leaves is at most `iselCost` of the expression, independently of the target and
temporary registers. -/

/-- Raw price of a move list. -/
def rawMovePrice (pairs : List (Nat × Nat)) : Nat := 24 * pairs.length

/-- Pre-allocation leaf budget: raw-priced moves, canonical otherwise. -/
def preAllocLeafBudget : WordLangProgHOL (BitVec 64) → Option Nat
  | .move _ pairs => some (rawMovePrice pairs)
  | p@(.inst _) | p@(.get _ _) | p@(.locValue _ _) | p@(.opCurrHeap _ _ _) =>
    (WordToStack.refinedWordStackLeafBudget p).map (max 24)
  | p => WordToStack.refinedWordStackLeafBudget p

/-- Static bound on the canonical cost of `instSelectExp` for an expression. -/
def iselCost : WordLangExpHOL (BitVec 64) → Nat
  | .const _ | .var _ | .lookup _ => 24
  | .load e => iselCost e + 24
  | .op _ [e1, e2] => iselCost e1 + iselCost e2 + 24
  | .op _ _ => 0
  | .shift _ e e1 => iselCost e + iselCost e1 + 28
termination_by e => sizeOf e

theorem iselCost_op2 (op : BinOp) (e1 e2 : WordLangExpHOL (BitVec 64)) :
    iselCost (.op op [e1, e2]) = iselCost e1 + iselCost e2 + 24 := by
  rw [iselCost]

theorem isel_const (c : Compiler.Encoders.Asm.AsmConfigExact 64) (tar temp : Nat) (w : BitVec 64) :
    lineBound preAllocLeafBudget (WordInst.instSelectExp c tar temp (.const w)) = some 24 := by
  rw [WordInst.instSelectExp.eq_def]
  simp [lineBound, isLeafProg, preAllocLeafBudget, WordToStack.refinedWordStackLeafBudget,
    WordToStack.refinedNativeInstructionPrice, Compiler.Encoders.Asm.HolInst.ofWordLangInst]

theorem isel_var (c : Compiler.Encoders.Asm.AsmConfigExact 64) (tar temp v : Nat) :
    lineBound preAllocLeafBudget (WordInst.instSelectExp c tar temp (.var v)) = some 24 := by
  rw [WordInst.instSelectExp.eq_def]
  simp [lineBound, isLeafProg, preAllocLeafBudget, rawMovePrice]

theorem isel_lookup (c : Compiler.Encoders.Asm.AsmConfigExact 64) (tar temp : Nat) (st : WordStoreHOL) :
    lineBound preAllocLeafBudget (WordInst.instSelectExp c tar temp (.lookup st)) = some 24 := by
  rw [WordInst.instSelectExp.eq_def]
  simp [lineBound, isLeafProg, preAllocLeafBudget, WordToStack.refinedWordStackLeafBudget]

@[simp] theorem iselCost_const (w : BitVec 64) : iselCost (.const w) = 24 := by rw [iselCost]
@[simp] theorem iselCost_var (v : Nat) : iselCost (.var v) = 24 := by rw [iselCost]
@[simp] theorem iselCost_lookup (st : WordStoreHOL) : iselCost (.lookup st) = 24 := by rw [iselCost]
@[simp] theorem iselCost_load (e : WordLangExpHOL (BitVec 64)) : iselCost (.load e) = iselCost e + 24 := by
  rw [iselCost]
@[simp] theorem iselCost_shift (sh : Shift) (e e1 : WordLangExpHOL (BitVec 64)) :
    iselCost (.shift sh e e1) = iselCost e + iselCost e1 + 28 := by rw [iselCost]

/-- Leaf part of a `seq`: an instruction or store leaf with a budget. -/
theorem lineBound_seq_of {a b : WordLangProgHOL (BitVec 64)} {x y : Nat}
    (ha : lineBound preAllocLeafBudget a = some x) (hb : lineBound preAllocLeafBudget b = some y) :
    lineBound preAllocLeafBudget (.seq a b) = some (x + y) := by
  simp [lineBound, ha, hb]

attribute [local simp] lineBound isLeafProg preAllocLeafBudget rawMovePrice
  WordToStack.refinedWordStackLeafBudget WordToStack.refinedNativeInstructionPrice
  Compiler.Encoders.Asm.HolInst.ofWordLangInst Compiler.Encoders.Asm.HolArith.ofWordLangArith Compiler.Encoders.Asm.HolRegImm.ofWordRegImm

/-- The selected code for an expression is straight-line and costs at most
`iselCost` under the pre-allocation leaf budget, for any target and temporary. -/
theorem isel_lineBound (c : Compiler.Encoders.Asm.AsmConfigExact 64) (tar temp : Nat) :
    ∀ e : WordLangExpHOL (BitVec 64),
      ∃ k, lineBound preAllocLeafBudget (WordInst.instSelectExp c tar temp e) = some k ∧ k ≤ iselCost e
  | .const w => ⟨24, isel_const c tar temp w, by simp⟩
  | .var v => ⟨24, isel_var c tar temp v, by simp⟩
  | .lookup st => ⟨24, isel_lookup c tar temp st, by simp⟩
  | .load exp => by
    rw [WordInst.instSelectExp.eq_def]
    simp only []
    split
    · rename_i exp' w
      split
      · obtain ⟨k, hk, hle⟩ := isel_lineBound c temp temp exp'
        refine ⟨k + 24, by simp [hk], ?_⟩
        simp [iselCost_op2]; omega
      · obtain ⟨k, hk, hle⟩ := isel_lineBound c temp temp (.op .add [exp', .const w])
        exact ⟨k + 24, by simp [hk], by simp; omega⟩
    · obtain ⟨k, hk, hle⟩ := isel_lineBound c temp temp exp
      exact ⟨k + 24, by simp [hk], by simp; omega⟩
  | .op op [e1, e2] => by
    rw [WordInst.instSelectExp.eq_def]
    simp only []
    obtain ⟨k1, hk1, hle1⟩ := isel_lineBound c temp temp e1
    obtain ⟨k2, hk2, hle2⟩ := isel_lineBound c temp temp e2
    rw [iselCost_op2]
    split
    · exact ⟨k1 + 24, by simp [hk1], by omega⟩
    · split
      · exact ⟨k2 + 24, by simp [hk2], by omega⟩
      · split
        · rename_i w _
          have h2 : iselCost (.const w) = 24 := by simp
          split
          · exact ⟨k1 + 24, by simp [hk1], by omega⟩
          · split
            · exact ⟨k1 + 24, by simp [hk1], by omega⟩
            · exact ⟨k1 + 48, by simp [hk1], by omega⟩
        · obtain ⟨k3, hk3, hle3⟩ := isel_lineBound c (temp + 1) (temp + 1) e2
          exact ⟨k1 + (k3 + 24), by simp [hk1, hk3], by omega⟩
  | .op op [] => ⟨0, by rw [WordInst.instSelectExp.eq_def] <;> simp <;> intro _ _ h <;> simp at h,
      by rw [iselCost] <;> first | omega | (intro _ _ h; simp at h)⟩
  | .op op [a] => ⟨0, by rw [WordInst.instSelectExp.eq_def] <;> simp <;> intro _ _ h <;> simp at h,
      by rw [iselCost] <;> first | omega | (intro _ _ h; simp at h)⟩
  | .op op (a :: b :: d :: rest) =>
    ⟨0, by rw [WordInst.instSelectExp.eq_def] <;> simp <;> intro _ _ h <;> simp at h,
      by rw [iselCost] <;> first | omega | (intro _ _ h; simp at h)⟩
  | .shift sh e e1 => by
    rw [WordInst.instSelectExp.eq_def]
    simp only []
    obtain ⟨k, hk, hle⟩ := isel_lineBound c temp temp e
    rw [iselCost_shift]
    split
    · rename_i shiftLen
      split
      · split
        · exact ⟨k + 24, by simp [hk], by simp; omega⟩
        · exact ⟨k + 24, by simp [hk], by simp; omega⟩
      · exact ⟨24, by simp, by omega⟩
    · obtain ⟨k1, hk1, hle1⟩ := isel_lineBound c (temp + 1) (temp + 1) e1
      exact ⟨k + (k1 + 28), by simp [hk, hk1], by omega⟩
termination_by e => sizeOf e

/-- Expression cost of a statement's selected expression. -/
noncomputable def selExpCost (e : WordLangExpHOL (BitVec 64)) : Nat :=
  iselCost (WordInst.flattenExp (WordInst.ExecutablePullExp.pullExpExecutable e))

theorem isel_assign_lineBound (c : Compiler.Encoders.Asm.AsmConfigExact 64) (temp v : Nat)
    (e : WordLangExpHOL (BitVec 64)) :
    ∃ k, lineBound preAllocLeafBudget (WordInst.instSelectExecutable c temp (.assign v e)) = some k ∧
      k ≤ selExpCost e := by
  simp only [WordInst.instSelectExecutable, selExpCost]
  exact isel_lineBound c v temp _

theorem isel_set_lineBound (c : Compiler.Encoders.Asm.AsmConfigExact 64) (temp : Nat)
    (st : WordStoreHOL) (e : WordLangExpHOL (BitVec 64)) :
    ∃ k, lineBound preAllocLeafBudget (WordInst.instSelectExecutable c temp (.set st e)) = some k ∧
      k ≤ selExpCost e + 12 := by
  simp only [WordInst.instSelectExecutable, selExpCost]
  obtain ⟨k, hk, hle⟩ := isel_lineBound c temp temp (WordInst.flattenExp (WordInst.ExecutablePullExp.pullExpExecutable e))
  exact ⟨k + 12, by simp [hk], by omega⟩

theorem isel_store_lineBound (c : Compiler.Encoders.Asm.AsmConfigExact 64) (temp v : Nat)
    (e : WordLangExpHOL (BitVec 64)) :
    ∃ k, lineBound preAllocLeafBudget (WordInst.instSelectExecutable c temp (.store e v)) = some k ∧
      k ≤ selExpCost e + 24 := by
  simp only [WordInst.instSelectExecutable, selExpCost]
  split
  · rename_i exp' w heq
    split
    · obtain ⟨k, hk, hle⟩ := isel_lineBound c temp temp exp'
      refine ⟨k + 24, by simp [hk], ?_⟩
      rw [heq, iselCost_op2]; simp; omega
    · obtain ⟨k, hk, hle⟩ := isel_lineBound c temp temp (.op .add [exp', .const w])
      exact ⟨k + 24, by rw [heq]; simp [hk], by rw [heq]; omega⟩
  · obtain ⟨k, hk, hle⟩ := isel_lineBound c temp temp (WordInst.flattenExp (WordInst.ExecutablePullExp.pullExpExecutable e))
    exact ⟨k + 24, by simp [hk], by omega⟩

/-- A pre-allocation leaf budget is what the intermediate optimizer price charges. -/
theorem refinedPrice_of_budget {C F : Type} {p : WordLangProgHOL (BitVec 64)} {b : Nat}
    (s : WordSemStateFiniteExact 64 C F) (h : WordToStack.refinedWordStackLeafBudget p = some b) :
    WordToStack.refinedWordLocalPrice p s = b := by
  simp only [WordToStack.refinedWordLocalPrice, h]

theorem optimizerPrice_le_preAllocLeaf {C F : Type} (p : WordLangProgHOL (BitVec 64))
    (s : WordSemStateFiniteExact 64 C F) (n : Nat) (leaf : isLeafProg p = true)
    (budget : preAllocLeafBudget p = some n) : wordOptimizerLocalPrice p s ≤ n := by
  cases p <;> simp only [isLeafProg, Bool.false_eq_true] at leaf
  case move priority pairs =>
    simp only [preAllocLeafBudget, rawMovePrice, Option.some.injEq] at budget
    subst budget; simp only [wordOptimizerLocalPrice]; exact Nat.le_refl _
  case inst i =>
    simp only [preAllocLeafBudget, Option.map_eq_some_iff] at budget
    obtain ⟨b, hb, rfl⟩ := budget
    simp only [wordOptimizerLocalPrice, refinedPrice_of_budget s hb, Nat.le_refl]
  case get r st =>
    simp only [preAllocLeafBudget, Option.map_eq_some_iff] at budget
    obtain ⟨b, hb, rfl⟩ := budget
    simp only [wordOptimizerLocalPrice, refinedPrice_of_budget s hb, Nat.le_refl]
  case locValue r l =>
    simp only [preAllocLeafBudget, Option.map_eq_some_iff] at budget
    obtain ⟨b, hb, rfl⟩ := budget
    simp only [wordOptimizerLocalPrice, refinedPrice_of_budget s hb, Nat.le_refl]
  case opCurrHeap o d r =>
    simp only [preAllocLeafBudget, Option.map_eq_some_iff] at budget
    obtain ⟨b, hb, rfl⟩ := budget
    simp only [wordOptimizerLocalPrice, refinedPrice_of_budget s hb, Nat.le_refl]
  all_goals
    simp only [preAllocLeafBudget] at budget
    simp only [wordOptimizerLocalPrice, refinedPrice_of_budget s budget, Nat.le_refl]

/-- Executed cost of instruction-selected code for an expression, from any
state, at the intermediate optimizer price. -/
theorem isel_exp_cost {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) (tar temp : Nat)
    (e : WordLangExpHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost wordOptimizerLocalPrice (WordInst.instSelectExp c tar temp e) s ≤ iselCost e := by
  obtain ⟨k, hk, hle⟩ := isel_lineBound c tar temp e
  have := wordCost_le_lineBound wordOptimizerLocalPrice preAllocLeafBudget
    (fun a b s => by simp [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
      WordToStack.refinedWordStackLeafBudget])
    (fun p s n leaf budget => optimizerPrice_le_preAllocLeaf p s n leaf budget) _ k hk s
  omega

#print axioms isel_lineBound
#print axioms optimizerPrice_le_preAllocLeaf
#print axioms isel_exp_cost
#print axioms isel_assign_lineBound
#print axioms isel_set_lineBound
#print axioms isel_store_lineBound
end InitECandidate.Runtime.FineCost
