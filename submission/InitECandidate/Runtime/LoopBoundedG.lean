import InitECandidate.Runtime.CrepSelLeaf
namespace InitECandidate.Runtime.FineCost
open Flapjack

/-! State-uniform executed-work ceilings for Loop code at any leaf price, in any
calling function, and allowances for expression-generated code. The default
`LoopWork` prices and the selector-derived prices are both instances. -/

/-- From every state, in every calling function, the actual run has a work
derivation within `bound`. -/
def LoopBoundedG (L : LeafPrice) (p : HolLoopProg 64) (bound : Nat) : Prop :=
  ∀ (F : Type) (f : Nat) (s : LoopSemStateFiniteExact 64 F), ∃ w,
    LoopWorkG L f s p (LoopSemStateFiniteExact.evaluate p s) w ∧ w ≤ bound

namespace LoopBoundedG
variable {L : LeafPrice}

theorem mono {p : HolLoopProg 64} {a b : Nat} (h : LoopBoundedG L p a) (le : a ≤ b) : LoopBoundedG L p b := by
  intro F f s; obtain ⟨w, work, bound⟩ := h F f s; exact ⟨w, work, by omega⟩

theorem leaf {p : HolLoopProg 64} {k b : Nat} (h : L.lf p = some k) (le : k ≤ b) : LoopBoundedG L p b :=
  fun _ _ _ => ⟨k, LoopWorkG.atom h rfl, le⟩

theorem seq {first second : HolLoopProg 64} {a b : Nat}
    (one : LoopBoundedG L first a) (two : LoopBoundedG L second b) : LoopBoundedG L (.seq first second) (a + b) := by
  intro F f s
  obtain ⟨w1, work1, bound1⟩ := one F f s
  rcases run : LoopSemStateFiniteExact.evaluate first s with ⟨_ | result, middle⟩
  · rw [run] at work1
    obtain ⟨w2, work2, bound2⟩ := two F f middle
    refine ⟨w1 + w2, ?_, by omega⟩
    have rule := LoopWorkG.seqNext work1 work2
    rwa [← LoopWorkG.sound rule] at rule
  · rw [run] at work1
    refine ⟨w1, ?_, by omega⟩
    have rule := LoopWorkG.seqStop (second := second) work1
    rwa [← LoopWorkG.sound rule] at rule

theorem ite {operator : Cmp} {register : Nat} {right : RegImm (BitVec 64)} {yes no : HolLoopProg 64}
    {live : NumSet} {a b : Nat} (yesB : LoopBoundedG L yes a) (noB : LoopBoundedG L no b) :
    LoopBoundedG L (.ite operator register right yes no live) (L.ite + max a b) := by
  intro F f s
  by_cases words : ∃ x y, sptLookup register s.locals = some (.word x) ∧
      LoopSemStateFiniteExact.getVarImm right s = some (.word y)
  · obtain ⟨x, y, hx, hy⟩ := words
    by_cases chosen : Compiler.Encoders.Asm.wordCmpHOL operator x y = true
    · obtain ⟨w, work, bound⟩ := yesB F f s
      have rule := LoopWorkG.iteBranch (live := live) (no := no) hx hy (by rw [if_pos chosen]; exact work)
      refine ⟨L.ite + w, ?_, by omega⟩
      rwa [← LoopWorkG.sound rule] at rule
    · obtain ⟨w, work, bound⟩ := noB F f s
      have rule := LoopWorkG.iteBranch (live := live) (yes := yes) hx hy (by rw [if_neg chosen]; exact work)
      refine ⟨L.ite + w, ?_, by omega⟩
      rwa [← LoopWorkG.sound rule] at rule
  · have rule := LoopWorkG.iteInvalid (L := L) (f := f) (live := live) (yes := yes) (no := no)
      (operator := operator) (s := s) words
    refine ⟨1, ?_, by have := L.iteOne; omega⟩
    rwa [← LoopWorkG.sound rule] at rule

theorem single {p : HolLoopProg 64} {k : Nat} (h : LoopBoundedG L p k) : LoopBoundedG L (loopNestedSeqHOL [p]) k := by
  have := seq h (leaf L.skip (Nat.le_refl 0))
  simpa [loopNestedSeqHOL] using this

end LoopBoundedG

/-- An allowance for expression-generated Loop statements at leaf price `L`:
a statement's allowance bounds its executed work. -/
structure CodeAllowance (L : LeafPrice) where
  work : HolLoopProg 64 → Option Nat
  sound : ∀ p k, work p = some k → LoopBoundedG L p k

/-- Allowance of a statement list. -/
def CodeAllowance.works {L : LeafPrice} (A : CodeAllowance L) : List (HolLoopProg 64) → Option Nat
  | [] => some 0
  | p :: ps => do
      let a ← A.work p
      let b ← A.works ps
      pure (a + b)

theorem CodeAllowance.codes_append {L : LeafPrice} (A : CodeAllowance L) :
    ∀ (codes rest : List (HolLoopProg 64)) (k b : Nat), A.works codes = some k →
      LoopBoundedG L (loopNestedSeqHOL rest) b → LoopBoundedG L (loopNestedSeqHOL (codes ++ rest)) (k + b)
  | [], rest, k, b, h, tail => by
    simp [CodeAllowance.works] at h; subst h; simpa using tail
  | head :: tail, rest, k, b, h, restBounded => by
    simp only [CodeAllowance.works] at h
    cases ha : A.work head <;> cases hb : A.works tail <;> simp_all
    rename_i x y
    subst h
    have := LoopBoundedG.seq (A.sound head x ha) (A.codes_append tail rest y b hb restBounded)
    simpa [loopNestedSeqHOL, Nat.add_assoc] using this

/-- Selector allowance at the selector-derived leaf price. -/
noncomputable def selAllowance (c : Compiler.Encoders.Asm.AsmConfigExact 64) : CodeAllowance (wsLeaf c) where
  work := selCodeWork
  sound := fun p k h F f s => selCodeWork_bounded c p k h F f s

theorem selAllowance_works (c : Compiler.Encoders.Asm.AsmConfigExact 64) :
    ∀ codes, (selAllowance c).works codes = selCodesWork codes
  | [] => rfl
  | p :: ps => by simp only [CodeAllowance.works, selCodesWork, selAllowance_works c ps]; rfl

/-- Default `LoopWork` ceilings are ceilings at the default leaf price in every calling function. -/
theorem LoopBounded.toG {p : HolLoopProg 64} {k : Nat} (h : LoopBounded p k) : LoopBoundedG defaultLeaf p k := by
  intro F f s
  obtain ⟨w, work, bound⟩ := h F s
  exact ⟨w, work.toG f, bound⟩

/-- The `LoopWork` allowance at the default leaf price. -/
def defaultAllowance : CodeAllowance defaultLeaf where
  work := loopExpressionCodeWork
  sound := fun p k h => (loopBounded_of_codeWork p k h).toG

#print axioms CodeAllowance.codes_append
#print axioms selAllowance_works
end InitECandidate.Runtime.FineCost
