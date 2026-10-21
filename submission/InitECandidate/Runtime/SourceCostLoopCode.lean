import InitECandidate.Runtime.SourceCostLoopWork
import InitECandidate.Runtime.CrepToLoopLocalBound
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

/-- A state-uniform executed-work ceiling for Loop code: from every state the
actual run has a work derivation within `bound`. -/
def LoopBounded (program : HolLoopProg 64) (bound : Nat) : Prop :=
  ∀ (F : Type) (s : LoopSemStateFiniteExact 64 F), ∃ w,
    LoopWork s program (evaluate program s) w ∧ w ≤ bound

theorem LoopBounded.mono {program : HolLoopProg 64} {small large : Nat}
    (bounded : LoopBounded program small) (le : small ≤ large) : LoopBounded program large := by
  intro F s
  obtain ⟨w, work, bound⟩ := bounded F s
  exact ⟨w, work, by omega⟩

theorem loopBounded_leaf {program : HolLoopProg 64} {cost : Nat}
    (leaf : loopWorkLeafCost program = some cost) : LoopBounded program cost :=
  fun _ s => ⟨cost, LoopWork.atom leaf rfl, Nat.le_refl _⟩

theorem loopBounded_seq {first second : HolLoopProg 64} {a b : Nat}
    (one : LoopBounded first a) (two : LoopBounded second b) :
    LoopBounded (.seq first second) (a + b) := by
  intro F s
  obtain ⟨w1, work1, bound1⟩ := one F s
  rcases run : evaluate first s with ⟨_ | result, middle⟩
  · rw [run] at work1
    obtain ⟨w2, work2, bound2⟩ := two F middle
    refine ⟨w1 + w2, ?_, by omega⟩
    have rule := LoopWork.seqNext work1 work2
    rwa [← LoopWork.sound rule] at rule
  · rw [run] at work1
    refine ⟨w1, ?_, by omega⟩
    have rule := LoopWork.seqStop (second := second) work1
    rwa [← LoopWork.sound rule] at rule

theorem loopBounded_ite {operator : Cmp} {register : Nat} {right : RegImm (BitVec 64)}
    {yes no : HolLoopProg 64} {live : NumSet} {a b : Nat}
    (yesBounded : LoopBounded yes a) (noBounded : LoopBounded no b) :
    LoopBounded (.ite operator register right yes no live) (37 + max a b) := by
  intro F s
  by_cases words : ∃ x y, sptLookup register s.locals = some (.word x) ∧
      LoopSemStateFiniteExact.getVarImm right s = some (.word y)
  · obtain ⟨x, y, hx, hy⟩ := words
    by_cases chosen : Compiler.Encoders.Asm.wordCmpHOL operator x y = true
    · obtain ⟨w, work, bound⟩ := yesBounded F s
      have rule := LoopWork.iteBranch (live := live) (no := no) hx hy
        (by rw [if_pos chosen]; exact work)
      refine ⟨37 + w, ?_, by omega⟩
      rwa [← LoopWork.sound rule] at rule
    · obtain ⟨w, work, bound⟩ := noBounded F s
      have rule := LoopWork.iteBranch (live := live) (yes := yes) hx hy
        (by rw [if_neg chosen]; exact work)
      refine ⟨37 + w, ?_, by omega⟩
      rwa [← LoopWork.sound rule] at rule
  · have rule := LoopWork.iteInvalid (live := live) (yes := yes) (no := no)
      (operator := operator) (s := s) words
    refine ⟨1, ?_, by omega⟩
    rwa [← LoopWork.sound rule] at rule

mutual
  /-- Generated expression code runs within its syntactic allowance from every
  state, following the actual branch and stopping on failure. -/
  theorem loopBounded_of_codeWork : ∀ (p : HolLoopProg 64) (c : Nat),
      loopExpressionCodeWork p = some c → LoopBounded p c
    | .skip, c, h => by
      simp [loopExpressionCodeWork] at h; subst h; exact loopBounded_leaf rfl
    | .assign name value, c, h => by
      simp [loopExpressionCodeWork] at h; subst h; exact loopBounded_leaf rfl
    | .arith op, c, h => by
      simp [loopExpressionCodeWork] at h; subst h; exact loopBounded_leaf rfl
    | .load32 a v, c, h => by
      simp [loopExpressionCodeWork] at h; subst h; exact loopBounded_leaf rfl
    | .loadByte a v, c, h => by
      simp [loopExpressionCodeWork] at h; subst h; exact loopBounded_leaf rfl
    | .seq first second, c, h => by
      simp only [loopExpressionCodeWork] at h
      cases ha : loopExpressionCodeWork first <;> cases hb : loopExpressionCodeWork second <;>
        simp_all
      rename_i a b
      subst h
      exact loopBounded_seq (loopBounded_of_codeWork first a ha)
        (loopBounded_of_codeWork second b hb)
    | .ite operator register right yes no live, c, h => by
      simp only [loopExpressionCodeWork] at h
      cases ha : loopExpressionCodeWork yes <;> cases hb : loopExpressionCodeWork no <;>
        simp_all
      rename_i a b
      subst h
      exact loopBounded_ite (loopBounded_of_codeWork yes a ha)
        (loopBounded_of_codeWork no b hb)
    | .primitive _ _ _, c, h | .store _ _, c, h | .setGlobal _ _, c, h | .store32 _ _, c, h
    | .storeByte _ _, c, h | .loop _ _ _, c, h | .break _, c, h | .continue _, c, h
    | .raise _, c, h | .return _, c, h | .shMem _ _ _, c, h | .tick, c, h | .mark _, c, h
    | .fail, c, h | .locValue _ _, c, h | .call _ _ _ _, c, h | .ffi _ _ _ _ _ _, c, h => by
      simp [loopExpressionCodeWork] at h
  termination_by p => sizeOf p
end

theorem loopBounded_nestedSeq_codes : ∀ (codes : List (HolLoopProg 64)) (c : Nat),
    loopExpressionCodesWork codes = some c → LoopBounded (loopNestedSeqHOL codes) c
  | [], c, h => by
    simp [loopExpressionCodesWork] at h; subst h
    exact loopBounded_leaf rfl
  | head :: tail, c, h => by
    simp only [loopExpressionCodesWork] at h
    cases ha : loopExpressionCodeWork head <;> cases hb : loopExpressionCodesWork tail <;>
      simp_all
    rename_i a b
    subst h
    exact loopBounded_seq (loopBounded_of_codeWork head a ha)
      (loopBounded_nestedSeq_codes tail b hb)

#print axioms loopBounded_of_codeWork
#print axioms loopBounded_nestedSeq_codes
end InitECandidate.Runtime.FineCost
