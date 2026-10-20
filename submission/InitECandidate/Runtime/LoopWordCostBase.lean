import InitECandidate.Runtime.LoopWordPrice
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Assembly
import Flapjack.Pancake.Proofs.LoopToWord.LocalsRelLookups
import Flapjack.Pancake.Proofs.LoopToWord.AccVarsAcc
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact

/-! The Loop-to-Word cost transfer: the shared motive and the cases without a
callee. The premises are exactly those of the pinned `compile_correct`. -/

/-- From any Word state related as in the pinned `compile_correct`, the
compiled program's executed Word work is at most the Loop work. -/
def WordCostLe (C : Type) {F : Type} (s : LoopSemStateFiniteExact 64 F) (p : HolLoopProg 64)
    (output : Option (LoopSemStateFiniteExact.LoopResultExact 64) × LoopSemStateFiniteExact 64 F)
    (w : Nat) : Prop :=
  output.1 ≠ some .error → ∀ (t : WordSemStateFiniteExact 64 C F) (ctxt : Spt Nat)
    (retv : WordLocW 64) (l : Nat × Nat),
    loopToWordStateRelHOLExact s t → LoopToWord.localsRelHOL ctxt s.locals t.locals →
    sptLookup 0 t.locals = some retv → goodDimindex 64 → ¬ wordSemIsWordLoc retv = true →
    (∀ k, sptMem k (accVarsHOL p .ln) → sptMem k ctxt) →
    wordExecutionCost loopWordPrice (LoopToWord.compHOL ctxt p l).1 t ≤ w

/-- The pinned `compile_correct`, specialised. -/
theorem word_run {C F : Type} {s : LoopSemStateFiniteExact 64 F} {p : HolLoopProg 64} {res s1}
    (run : LoopSemStateFiniteExact.evaluate p s = (res, s1)) (ok : res ≠ some .error)
    {t : WordSemStateFiniteExact 64 C F} {ctxt : Spt Nat} {retv : WordLocW 64} (l : Nat × Nat)
    (rel : loopToWordStateRelHOLExact s t) (locals : LoopToWord.localsRelHOL ctxt s.locals t.locals)
    (ret : sptLookup 0 t.locals = some retv) (dim : goodDimindex 64)
    (notWord : ¬ wordSemIsWordLoc retv = true) (acc : ∀ k, sptMem k (accVarsHOL p .ln) → sptMem k ctxt) :
    ∃ t1 res1, WordSemStateFiniteExact.evaluate (LoopToWord.compHOL ctxt p l).1 t = (res1, t1) ∧
      t1.ffi = s1.ffi ∧ LoopToWord.CompileCorrect.resultCase ctxt retv t res s1 res1 t1 :=
  compileCorrect p s res s1 t ctxt retv l ⟨run, ok, rel, locals, ret, dim, notWord, acc⟩

theorem acc_split {a b : HolLoopProg 64} {ctxt : Spt Nat}
    (acc : ∀ k, sptMem k (accVarsHOL a (accVarsHOL b .ln)) → sptMem k ctxt) :
    (∀ k, sptMem k (accVarsHOL a .ln) → sptMem k ctxt) ∧
      (∀ k, sptMem k (accVarsHOL b .ln) → sptMem k ctxt) := by
  have split : ∀ k, sptMem k (accVarsHOL a (accVarsHOL b .ln)) ↔
      sptMem k (accVarsHOL a .ln) ∨ sptMem k (accVarsHOL b .ln) := by
    intro k
    change sptDomain (accVarsHOL a (accVarsHOL b .ln)) k ↔
      sptDomain (accVarsHOL a .ln) k ∨ sptDomain (accVarsHOL b .ln) k
    rw [accVarsAccHOL a (accVarsHOL b .ln)]
  exact ⟨fun k hk => acc k ((split k).2 (Or.inl hk)), fun k hk => acc k ((split k).2 (Or.inr hk))⟩

theorem compHOL_seq (ctxt : Spt Nat) (a b : HolLoopProg 64) (l : Nat × Nat) :
    (LoopToWord.compHOL ctxt (.seq a b) l).1 =
      .seq (LoopToWord.compHOL ctxt a l).1 (LoopToWord.compHOL ctxt b (LoopToWord.compHOL ctxt a l).2).1 := by
  simp only [LoopToWord.compHOL]

theorem wordCostLe_atom {C F : Type} {s : LoopSemStateFiniteExact 64 F} {p output cost}
    (leaf : loopWorkLeafCost p = some cost) : WordCostLe C s p output cost := by
  intro _ t ctxt _ l _ _ _ _ _ _
  exact loop_word_leaf ctxt p l cost leaf t

theorem wordCostLe_mark {C F : Type} {s : LoopSemStateFiniteExact 64 F} {p output w}
    (ih : WordCostLe C s p output w) : WordCostLe C s (.mark p) output w := by
  intro ok t ctxt retv l rel locals ret dim notWord acc
  simp only [LoopToWord.compHOL]
  exact ih ok t ctxt retv l rel locals ret dim notWord (by simpa [accVarsHOL] using acc)

theorem wordCostLe_seqNext {C F : Type} {s middle : LoopSemStateFiniteExact 64 F} {first second output a b}
    (one : LoopWork s first (none, middle) a)
    (ih1 : WordCostLe C s first (none, middle) a) (ih2 : WordCostLe C middle second output b) :
    WordCostLe C s (.seq first second) output (a + b) := by
  intro ok t ctxt retv l rel locals ret dim notWord acc
  obtain ⟨acc1, acc2⟩ := acc_split (by simpa only [accVarsHOL] using acc)
  obtain ⟨t1, res1, run1, -, rc⟩ := word_run one.sound (by simp) l rel locals ret dim notWord acc1
  obtain ⟨rel1, rfl, ret1, locals1, -, -⟩ := rc
  have c1 := ih1 (by simp) t ctxt retv l rel locals ret dim notWord acc1
  have c2 := ih2 ok t1 ctxt retv (LoopToWord.compHOL ctxt first l).2 rel1 locals1 ret1 dim notWord acc2
  rw [compHOL_seq, wordExecutionCost_seq, run1]
  simp only [loopWordPrice]
  omega

theorem wordCostLe_seqStop {C F : Type} {s post : LoopSemStateFiniteExact 64 F} {first second result a}
    (one : LoopWork s first (some result, post) a) (ih1 : WordCostLe C s first (some result, post) a) :
    WordCostLe C s (.seq first second) (some result, post) a := by
  intro ok t ctxt retv l rel locals ret dim notWord acc
  obtain ⟨acc1, -⟩ := acc_split (by simpa only [accVarsHOL] using acc)
  obtain ⟨t1, res1, run1, -, rc⟩ := word_run one.sound ok l rel locals ret dim notWord acc1
  have c1 := ih1 ok t ctxt retv l rel locals ret dim notWord acc1
  have stop : res1 ≠ none := by
    intro h; subst h
    cases result <;> simp_all [LoopToWord.CompileCorrect.resultCase]
  rw [compHOL_seq, wordExecutionCost_seq, run1]
  rcases res1 with _ | r
  · exact absurd rfl stop
  · simp only [loopWordPrice]; omega

theorem wordCostLe_iteBranch {C F : Type} {s : LoopSemStateFiniteExact 64 F}
    {operator register right yes no live x y output w}
    (lhs : sptLookup register s.locals = some (.word x))
    (rhs : LoopSemStateFiniteExact.getVarImm right s = some (.word y))
    (ih : WordCostLe C s (if Compiler.Encoders.Asm.wordCmpHOL operator x y then yes else no) output w)
    (ok' : output.1 = some .error → (LoopSemStateFiniteExact.cutRes live output).1 = some .error) :
    WordCostLe C s (.ite operator register right yes no live) (LoopSemStateFiniteExact.cutRes live output)
      (2 + w) := by
  intro ok t ctxt retv l rel locals ret dim notWord acc
  obtain ⟨acc1, acc2⟩ := acc_split (by simpa only [accVarsHOL] using acc)
  have okb : output.1 ≠ some .error := fun h => ok (ok' h)
  have htx := LoopToWord.localsRelHOLGetVar ctxt s.locals t register (.word x) ⟨locals, lhs⟩
  rcases hc1 : LoopToWord.compHOL ctxt yes l with ⟨w1, l1⟩
  rcases hc2 : LoopToWord.compHOL ctxt no l1 with ⟨w2, l2⟩
  obtain ⟨targetRi, unfold, hty⟩ : ∃ ri : WordRegImm (BitVec 64),
      (LoopToWord.compHOL ctxt (.ite operator register right yes no live) l).1 =
        .seq (.ite operator (LoopToWord.findVarHOL ctxt register) ri w1 w2) .tick ∧
      WordSemStateFiniteExact.getVarImm ri t = some (.word y) := by
    unfold LoopToWord.compHOL
    simp only [hc1, hc2]
    cases right with
    | imm v => exact ⟨_, rfl, by simpa [LoopSemStateFiniteExact.getVarImm, WordSemStateFiniteExact.getVarImm] using rhs⟩
    | reg n => exact ⟨_, rfl, LoopToWord.localsRelHOLGetVar ctxt s.locals t n (.word y) ⟨locals, rhs⟩⟩
  rw [unfold]
  refine Nat.le_trans (wordCost_seq_le _ _ _ _ 1 fun m => by rw [wordCost_tick]; simp [loopWordPrice]) ?_
  rw [wordExecutionCost]
  simp only [htx, hty, wordSemWordCmp, loopWordPrice]
  cases hb : Compiler.Encoders.Asm.wordCmpHOL operator x y
  · have := ih okb t ctxt retv l1 rel locals ret dim notWord (by simpa [hb] using acc2)
    simp only [hb, Bool.false_eq_true, ↓reduceIte, hc2] at this
    dsimp only
    omega
  · have := ih okb t ctxt retv l rel locals ret dim notWord (by simpa [hb] using acc1)
    simp only [hb, ↓reduceIte, hc1] at this
    dsimp only
    omega

#print axioms wordCostLe_seqNext
#print axioms wordCostLe_seqStop
#print axioms wordCostLe_iteBranch
#print axioms wordCostLe_mark
#print axioms wordCostLe_atom
end InitECandidate.Runtime.FineCost
