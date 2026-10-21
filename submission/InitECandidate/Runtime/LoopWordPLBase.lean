import InitECandidate.Runtime.LoopWordPLLabels
import InitECandidate.Runtime.LoopWorkPL
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact

/-! Label-indexed parametric Loop-to-Word transfer: base cases. -/


open Classical in
/-- Local domination of a Word price by a Loop price. Structural composition is
free; ticks, conditionals and loop nodes have uniform bounds; every compiled
non-recursive Loop statement costs at most its Loop leaf price; calls pay a
unit, an arity-dependent argument charge, and (returning calls) each returned word only when the
callee returns that arity. -/
structure WordDominatesL {C F : Type} (wp : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (lp : LoopPriceL) where
  T : Nat
  I : Nat
  L : Nat
  U : Nat
  argW : Nat → Nat
  R : Nat
  seqZero : ∀ a b s, wp (.seq a b) s = 0
  skipZero : ∀ s, wp .skip s = 0
  tick : ∀ s, wp .tick s ≤ T
  ite : ∀ cmp r ri a b s, wp (.ite cmp r ri a b) s ≤ I
  loop : ∀ n b e s, wp (.loop n b e) s ≤ L
  leafOk : ∀ (ctxt : Spt Nat) (p : HolLoopProg 64) (l : Nat × Nat) (s : WordSemStateFiniteExact 64 C F) cost,
    lp.base.leaf p = some cost → wordExecutionCost wp (LoopToWord.compHOL ctxt p l).1 s ≤ cost
  tailCall : ∀ d args h s, wp (.call none d args h) s ≤ U + argW (args.length - 1) + lp.tail d
  retCall : ∀ rets cut rc l1 l2 d args h s,
    wp (.call (some (rets, cut, rc, l1, l2)) d args h) s ≤
      U + argW args.length +
        (if wordCallReturned (.call (some (rets, cut, rc, l1, l2)) d args h) s then R * rets.length else 0) +
          lp.site (l1, l2) d + lp.retNames rets.length
  iteOk : I + T ≤ lp.base.ite
  iterOk : 2 * T + L ≤ lp.base.iter
  tailOk : U ≤ lp.base.call
  argOk : ∀ n, argW n ≤ lp.base.argCost n
  retOk : R ≤ lp.base.ret
  contOk : T ≤ lp.base.cont

/-- The parametric motive. -/
def WordCostLePL (C : Type) {F : Type} (wp : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (s : LoopSemStateFiniteExact 64 F) (p : HolLoopProg 64) (l : Nat × Nat)
    (output : Option (LoopSemStateFiniteExact.LoopResultExact 64) × LoopSemStateFiniteExact 64 F)
    (w : Nat) : Prop :=
  output.1 ≠ some .error → ∀ (t : WordSemStateFiniteExact 64 C F) (ctxt : Spt Nat)
    (retv : WordLocW 64),
    loopToWordStateRelHOLExact s t → LoopToWord.localsRelHOL ctxt s.locals t.locals →
    sptLookup 0 t.locals = some retv → goodDimindex 64 → ¬ wordSemIsWordLoc retv = true →
    (∀ k, sptMem k (accVarsHOL p .ln) → sptMem k ctxt) →
    wordExecutionCost wp (LoopToWord.compHOL ctxt p l).1 t ≤ w

section
variable {C F : Type} {wp : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat}
  {lp : LoopPriceL}

theorem wordCostLePL_atom (D : WordDominatesL wp lp) {s : LoopSemStateFiniteExact 64 F} {p output cost}
    {l : Nat × Nat} (leaf : lp.base.leaf p = some cost) : WordCostLePL C wp s p l output cost := by
  intro _ t ctxt _ _ _ _ _ _ _
  exact D.leafOk ctxt p l t cost leaf

theorem wordCostLePL_mark {s : LoopSemStateFiniteExact 64 F} {p output w} {l : Nat × Nat}
    (ih : WordCostLePL C wp s p l output w) : WordCostLePL C wp s (.mark p) l output w := by
  intro ok t ctxt retv rel locals ret dim notWord acc
  simp only [LoopToWord.compHOL]
  exact ih ok t ctxt retv rel locals ret dim notWord (by simpa [accVarsHOL] using acc)

theorem wordCostLePL_seqNext (D : WordDominatesL wp lp) {s middle : LoopSemStateFiniteExact 64 F}
    {first second output a b} {l : Nat × Nat}
    (one : LoopWorkPL lp l s first (none, middle) a)
    (ih1 : WordCostLePL C wp s first l (none, middle) a) (ih2 : WordCostLePL C wp middle second (labAfter first l) output b) :
    WordCostLePL C wp s (.seq first second) l output (a + b) := by
  intro ok t ctxt retv rel locals ret dim notWord acc
  obtain ⟨acc1, acc2⟩ := acc_split (by simpa only [accVarsHOL] using acc)
  obtain ⟨t1, res1, run1, -, rc⟩ := word_run one.sound (by simp) l rel locals ret dim notWord acc1
  obtain ⟨rel1, rfl, ret1, locals1, -, -⟩ := rc
  have c1 := ih1 (by simp) t ctxt retv rel locals ret dim notWord acc1
  have c2 := ih2 ok t1 ctxt retv rel1 locals1 ret1 dim notWord acc2
  rw [show labAfter first l = (LoopToWord.compHOL ctxt first l).2 from (compHOL_labAfter ctxt first l).symm] at c2
  rw [compHOL_seq, wordExecutionCost_seq, run1, D.seqZero]
  simp only
  omega

theorem wordCostLePL_seqStop (D : WordDominatesL wp lp) {s post : LoopSemStateFiniteExact 64 F}
    {first second result a} {l : Nat × Nat}
    (one : LoopWorkPL lp l s first (some result, post) a) (ih1 : WordCostLePL C wp s first l (some result, post) a) :
    WordCostLePL C wp s (.seq first second) l (some result, post) a := by
  intro ok t ctxt retv rel locals ret dim notWord acc
  obtain ⟨acc1, -⟩ := acc_split (by simpa only [accVarsHOL] using acc)
  obtain ⟨t1, res1, run1, -, rc⟩ := word_run one.sound ok l rel locals ret dim notWord acc1
  have c1 := ih1 ok t ctxt retv rel locals ret dim notWord acc1
  have stop : res1 ≠ none := by
    intro h; subst h
    cases result <;> simp_all [LoopToWord.CompileCorrect.resultCase]
  rw [compHOL_seq, wordExecutionCost_seq, run1, D.seqZero]
  rcases res1 with _ | r
  · exact absurd rfl stop
  · simp only; omega

theorem wordCostLePL_iteBranch (D : WordDominatesL wp lp) {s : LoopSemStateFiniteExact 64 F}
    {operator register right yes no live x y output w} {l : Nat × Nat}
    (lhs : sptLookup register s.locals = some (.word x))
    (rhs : LoopSemStateFiniteExact.getVarImm right s = some (.word y))
    (ih : WordCostLePL C wp s (if Compiler.Encoders.Asm.wordCmpHOL operator x y then yes else no)
      (if Compiler.Encoders.Asm.wordCmpHOL operator x y then l else labAfter yes l) output w)
    (ok' : output.1 = some .error → (LoopSemStateFiniteExact.cutRes live output).1 = some .error) :
    WordCostLePL C wp s (.ite operator register right yes no live) l (LoopSemStateFiniteExact.cutRes live output)
      (lp.base.ite + w) := by
  intro ok t ctxt retv rel locals ret dim notWord acc
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
  refine Nat.le_trans (wordCost_seq_le _ _ _ _ D.T fun m => by rw [wordCost_tick]; exact D.tick m) ?_
  rw [D.seqZero]
  have hI := D.ite operator (LoopToWord.findVarHOL ctxt register) targetRi w1 w2 t
  have hIT := D.iteOk
  rw [wordExecutionCost]
  simp only [htx, hty, wordSemWordCmp]
  cases hb : Compiler.Encoders.Asm.wordCmpHOL operator x y
  · have := ih okb t ctxt retv rel locals ret dim notWord (by simpa [hb] using acc2)
    have hl1 : labAfter yes l = l1 := by rw [← compHOL_labAfter ctxt yes l, hc1]
    simp only [hb, Bool.false_eq_true, ↓reduceIte, hl1, hc2] at this
    dsimp only
    omega
  · have := ih okb t ctxt retv rel locals ret dim notWord (by simpa [hb] using acc1)
    simp only [hb, ↓reduceIte, hc1] at this
    dsimp only
    omega
end


#print axioms wordCostLePL_atom
#print axioms wordCostLePL_seqNext
#print axioms wordCostLePL_iteBranch
end InitECandidate.Runtime.FineCost
