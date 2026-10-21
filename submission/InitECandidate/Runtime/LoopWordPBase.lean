import InitECandidate.Runtime.SourceCostLoopWorkP
import InitECandidate.Runtime.LoopWordCostBase
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact

/-! The price-parametric Loop-to-Word transfer: any Word price that is
dominated, node by node, by a Loop price. -/

open Classical in
/-- Local domination of a Word price by a Loop price. Structural composition is
free; ticks, conditionals and loop nodes have uniform bounds; every compiled
non-recursive Loop statement costs at most its Loop leaf price; calls pay a
unit, an arity-dependent argument charge, and (returning calls) each returned word only when the
callee returns that arity. -/
structure WordDominates {C F : Type} (wp : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (lp : LoopPrice) where
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
    lp.leaf p = some cost → wordExecutionCost wp (LoopToWord.compHOL ctxt p l).1 s ≤ cost
  tailCall : ∀ d args h s, wp (.call none d args h) s ≤ U + argW (args.length - 1)
  retCall : ∀ rets cut rc l1 l2 d args h s,
    wp (.call (some (rets, cut, rc, l1, l2)) d args h) s ≤
      U + argW args.length +
        if wordCallReturned (.call (some (rets, cut, rc, l1, l2)) d args h) s then R * rets.length else 0
  iteOk : I + T ≤ lp.ite
  iterOk : 2 * T + L ≤ lp.iter
  tailOk : U ≤ lp.call
  argOk : ∀ n, argW n ≤ lp.argCost n
  retOk : R ≤ lp.ret
  contOk : T ≤ lp.cont

/-- The parametric motive. -/
def WordCostLeP (C : Type) {F : Type} (wp : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (s : LoopSemStateFiniteExact 64 F) (p : HolLoopProg 64)
    (output : Option (LoopSemStateFiniteExact.LoopResultExact 64) × LoopSemStateFiniteExact 64 F)
    (w : Nat) : Prop :=
  output.1 ≠ some .error → ∀ (t : WordSemStateFiniteExact 64 C F) (ctxt : Spt Nat)
    (retv : WordLocW 64) (l : Nat × Nat),
    loopToWordStateRelHOLExact s t → LoopToWord.localsRelHOL ctxt s.locals t.locals →
    sptLookup 0 t.locals = some retv → goodDimindex 64 → ¬ wordSemIsWordLoc retv = true →
    (∀ k, sptMem k (accVarsHOL p .ln) → sptMem k ctxt) →
    wordExecutionCost wp (LoopToWord.compHOL ctxt p l).1 t ≤ w

section
variable {C F : Type} {wp : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat}
  {lp : LoopPrice}

theorem wordCostLeP_atom (D : WordDominates wp lp) {s : LoopSemStateFiniteExact 64 F} {p output cost}
    (leaf : lp.leaf p = some cost) : WordCostLeP C wp s p output cost := by
  intro _ t ctxt _ l _ _ _ _ _ _
  exact D.leafOk ctxt p l t cost leaf

theorem wordCostLeP_mark {s : LoopSemStateFiniteExact 64 F} {p output w}
    (ih : WordCostLeP C wp s p output w) : WordCostLeP C wp s (.mark p) output w := by
  intro ok t ctxt retv l rel locals ret dim notWord acc
  simp only [LoopToWord.compHOL]
  exact ih ok t ctxt retv l rel locals ret dim notWord (by simpa [accVarsHOL] using acc)

theorem wordCostLeP_seqNext (D : WordDominates wp lp) {s middle : LoopSemStateFiniteExact 64 F}
    {first second output a b}
    (one : LoopWorkP lp s first (none, middle) a)
    (ih1 : WordCostLeP C wp s first (none, middle) a) (ih2 : WordCostLeP C wp middle second output b) :
    WordCostLeP C wp s (.seq first second) output (a + b) := by
  intro ok t ctxt retv l rel locals ret dim notWord acc
  obtain ⟨acc1, acc2⟩ := acc_split (by simpa only [accVarsHOL] using acc)
  obtain ⟨t1, res1, run1, -, rc⟩ := word_run one.sound (by simp) l rel locals ret dim notWord acc1
  obtain ⟨rel1, rfl, ret1, locals1, -, -⟩ := rc
  have c1 := ih1 (by simp) t ctxt retv l rel locals ret dim notWord acc1
  have c2 := ih2 ok t1 ctxt retv (LoopToWord.compHOL ctxt first l).2 rel1 locals1 ret1 dim notWord acc2
  rw [compHOL_seq, wordExecutionCost_seq, run1, D.seqZero]
  simp only
  omega

theorem wordCostLeP_seqStop (D : WordDominates wp lp) {s post : LoopSemStateFiniteExact 64 F}
    {first second result a}
    (one : LoopWorkP lp s first (some result, post) a) (ih1 : WordCostLeP C wp s first (some result, post) a) :
    WordCostLeP C wp s (.seq first second) (some result, post) a := by
  intro ok t ctxt retv l rel locals ret dim notWord acc
  obtain ⟨acc1, -⟩ := acc_split (by simpa only [accVarsHOL] using acc)
  obtain ⟨t1, res1, run1, -, rc⟩ := word_run one.sound ok l rel locals ret dim notWord acc1
  have c1 := ih1 ok t ctxt retv l rel locals ret dim notWord acc1
  have stop : res1 ≠ none := by
    intro h; subst h
    cases result <;> simp_all [LoopToWord.CompileCorrect.resultCase]
  rw [compHOL_seq, wordExecutionCost_seq, run1, D.seqZero]
  rcases res1 with _ | r
  · exact absurd rfl stop
  · simp only; omega

theorem wordCostLeP_iteBranch (D : WordDominates wp lp) {s : LoopSemStateFiniteExact 64 F}
    {operator register right yes no live x y output w}
    (lhs : sptLookup register s.locals = some (.word x))
    (rhs : LoopSemStateFiniteExact.getVarImm right s = some (.word y))
    (ih : WordCostLeP C wp s (if Compiler.Encoders.Asm.wordCmpHOL operator x y then yes else no) output w)
    (ok' : output.1 = some .error → (LoopSemStateFiniteExact.cutRes live output).1 = some .error) :
    WordCostLeP C wp s (.ite operator register right yes no live) (LoopSemStateFiniteExact.cutRes live output)
      (lp.ite + w) := by
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
  refine Nat.le_trans (wordCost_seq_le _ _ _ _ D.T fun m => by rw [wordCost_tick]; exact D.tick m) ?_
  rw [D.seqZero]
  have hI := D.ite operator (LoopToWord.findVarHOL ctxt register) targetRi w1 w2 t
  have hIT := D.iteOk
  rw [wordExecutionCost]
  simp only [htx, hty, wordSemWordCmp]
  cases hb : Compiler.Encoders.Asm.wordCmpHOL operator x y
  · have := ih okb t ctxt retv l1 rel locals ret dim notWord (by simpa [hb] using acc2)
    simp only [hb, Bool.false_eq_true, ↓reduceIte, hc2] at this
    dsimp only
    omega
  · have := ih okb t ctxt retv l rel locals ret dim notWord (by simpa [hb] using acc1)
    simp only [hb, ↓reduceIte, hc1] at this
    dsimp only
    omega
end

#print axioms wordCostLeP_atom
#print axioms wordCostLeP_mark
#print axioms wordCostLeP_seqNext
#print axioms wordCostLeP_seqStop
#print axioms wordCostLeP_iteBranch
end InitECandidate.Runtime.FineCost
