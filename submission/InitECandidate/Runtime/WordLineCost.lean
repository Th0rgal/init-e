import InitECandidate.Runtime.LoopWordPrice
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact

/-! Static executed-cost bounds for straight-line Word code. A straight-line
program is a `seq` tree of leaves (no `ite`, `loop`, `call` or `mustTerminate`).
Under any price that charges nothing for `seq`, its executed cost from any
state is at most the sum of its leaf bounds, whether the run falls through or
stops early: an early stop only drops the remaining leaves. -/

/-- Leaves: nodes whose executed cost is their own local price. -/
def isLeafProg : WordLangProgHOL (BitVec 64) → Bool
  | .seq _ _ | .ite _ _ _ _ _ | .loop _ _ _ | .call _ _ _ _ | .mustTerminate _ => false
  | _ => true

theorem wordCost_leaf {C F : Type} (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    {p : WordLangProgHOL (BitVec 64)} (leaf : isLeafProg p = true) (s : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost price p s = price p s := by
  cases p <;> simp only [isLeafProg, Bool.false_eq_true] at leaf <;> rw [wordExecutionCost] <;> simp

/-- Sum of the leaf bounds of a straight-line program; `none` if a node is not
straight-line or has no leaf bound. -/
def lineBound (leaf : WordLangProgHOL (BitVec 64) → Option Nat) : WordLangProgHOL (BitVec 64) → Option Nat
  | .seq a b =>
    match lineBound leaf a, lineBound leaf b with
    | some x, some y => some (x + y)
    | _, _ => none
  | p => if isLeafProg p then leaf p else none

theorem lineBound_seq {leaf : WordLangProgHOL (BitVec 64) → Option Nat} {a b : WordLangProgHOL (BitVec 64)}
    {n : Nat} (h : lineBound leaf (.seq a b) = some n) :
    ∃ x y, lineBound leaf a = some x ∧ lineBound leaf b = some y ∧ n = x + y := by
  simp only [lineBound] at h
  split at h
  · rename_i x y hx hy
    exact ⟨x, y, hx, hy, (Option.some.inj h).symm⟩
  · cases h

theorem lineBound_leaf {leaf : WordLangProgHOL (BitVec 64) → Option Nat} {p : WordLangProgHOL (BitVec 64)}
    {n : Nat} (notSeq : ∀ a b, p ≠ .seq a b) (h : lineBound leaf p = some n) :
    isLeafProg p = true ∧ leaf p = some n := by
  cases p
  case seq a b => exact absurd rfl (notSeq a b)
  all_goals
    simp only [lineBound] at h
    split at h
    · exact ⟨by assumption, h⟩
    · cases h

/-- Executed cost of straight-line code is at most its static leaf sum. -/
theorem wordCost_le_lineBound {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (leaf : WordLangProgHOL (BitVec 64) → Option Nat)
    (seqZero : ∀ a b s, price (.seq a b) s = 0)
    (leafOk : ∀ p s n, isLeafProg p = true → leaf p = some n → price p s ≤ n) :
    ∀ (p : WordLangProgHOL (BitVec 64)) (n : Nat), lineBound leaf p = some n →
      ∀ s, wordExecutionCost price p s ≤ n
  | .seq a b, n, h, s => by
    obtain ⟨x, y, hx, hy, rfl⟩ := lineBound_seq h
    have ha := wordCost_le_lineBound price leaf seqZero leafOk a x hx s
    have := wordCost_seq_le price s a b y (fun m => wordCost_le_lineBound price leaf seqZero leafOk b y hy m)
    rw [seqZero] at this
    omega
  | p, n, h, s => by
    by_cases hs : ∃ a b, p = .seq a b
    · obtain ⟨a, b, rfl⟩ := hs
      obtain ⟨x, y, hx, hy, rfl⟩ := lineBound_seq h
      have ha := wordCost_le_lineBound price leaf seqZero leafOk a x hx s
      have := wordCost_seq_le price s a b y (fun m => wordCost_le_lineBound price leaf seqZero leafOk b y hy m)
      rw [seqZero] at this
      omega
    · obtain ⟨isLeaf, hn⟩ := lineBound_leaf (fun a b e => hs ⟨a, b, e⟩) h
      rw [wordCost_leaf price isLeaf]
      exact leafOk p s n isLeaf hn

#print axioms wordCost_leaf
#print axioms wordCost_le_lineBound
end InitECandidate.Runtime.FineCost
