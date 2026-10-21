import InitECandidate.Runtime.CrepLoopPricingG
namespace InitECandidate.Runtime.FineCost
open Flapjack

/-! Compiled non-recursive Crep statements at a generic Loop pricing: their
actual Loop execution, from any state and in any calling function, is within
`LoopPricingG.leafPrice`. -/

namespace LoopPricingG
variable (P : LoopPricingG)

theorem bounded_lf {p : HolLoopProg 64} {b : Nat} (h : ∃ k, P.L.lf p = some k ∧ k ≤ b) :
    LoopBoundedG P.L p b := by
  obtain ⟨k, hk, le⟩ := h; exact LoopBoundedG.leaf hk le

theorem bounded_skip {b : Nat} : LoopBoundedG P.L .skip b := LoopBoundedG.leaf P.L.skip (Nat.zero_le _)

theorem expr_tail (context : CrepToLoopContextExact) (tmp : Nat) (live : NumSet) (e : CrepExpHOL 64)
    (rest : List (HolLoopProg 64)) (b : Nat)
    (tail : LoopBoundedG P.L (loopNestedSeqHOL rest) (P.vp (compileExpHOLExact context tmp live e).2.1 + b)) :
    LoopBoundedG P.L (loopNestedSeqHOL ((compileExpHOLExact context tmp live e).1 ++ rest)) (P.price e + b) := by
  obtain ⟨cost, supported, bound⟩ := P.exprOk context tmp live e
  exact (P.A.codes_append _ rest cost _ supported tail).mono (by omega)

/-- Every non-recursive Crep statement compiles to Loop code within its price. -/
theorem leaf_compile (context : CrepToLoopContextExact) (live : NumSet) (p : CrepProgHOL 64) (k : Nat)
    (leaf : P.leafPrice p = some k) : LoopBoundedG P.L (compileHOLExact context live p) k := by
  cases p with
  | skip =>
    simp [leafPrice] at leaf; subst leaf; rw [compileHOLExact]; exact P.bounded_skip
  | tick =>
    simp [leafPrice] at leaf; subst leaf; rw [compileHOLExact]; exact P.bounded_lf P.tickOk
  | «break» l =>
    simp [leafPrice] at leaf; subst leaf; rw [compileHOLExact]; exact P.bounded_lf (P.breakOk l)
  | «continue» l =>
    simp [leafPrice] at leaf; subst leaf; rw [compileHOLExact]; exact P.bounded_lf (P.contOk l)
  | raise e =>
    simp [leafPrice] at leaf; subst leaf
    simp only [compileHOLExact]
    obtain ⟨k1, h1, b1⟩ := P.assignOk (context.vmax + 1) (.const e)
    have c1 := P.constOk e
    exact (LoopBoundedG.seq (LoopBoundedG.leaf h1 (Nat.le_refl _)) (P.bounded_lf (P.raiseOk _))).mono
      (by omega)
  | extCall f a b c d =>
    simp [leafPrice] at leaf; subst leaf
    simp only [compileHOLExact]
    split
    · exact P.bounded_lf (P.ffiOk _ _ _ _ _ _)
    · exact P.bounded_skip
  | primitive names op args =>
    simp [leafPrice] at leaf; subst leaf
    simp only [compileHOLExact]
    split
    · exact P.bounded_lf (P.primOk _ _ _)
    · exact P.bounded_skip
  | assign name value =>
    simp [leafPrice] at leaf; subst leaf
    simp only [compileHOLExact]
    split
    · exact P.bounded_skip
    · rename_i m _
      have := P.expr_tail context (context.vmax + 1) live value _ 0
        (LoopBoundedG.single (P.bounded_lf (P.assignOk m _)))
      simpa using this
  | storeGlob address value =>
    simp [leafPrice] at leaf; subst leaf
    simp only [compileHOLExact]
    exact P.expr_tail context (context.vmax + 1) live value _ _
      (LoopBoundedG.single (P.bounded_lf (P.setOk address _)))
  | shMem op name address =>
    simp [leafPrice] at leaf; subst leaf
    simp only [compileHOLExact]
    split
    · exact P.bounded_skip
    · rename_i m _
      exact P.expr_tail context (context.vmax + 1) live address _ _
        (LoopBoundedG.single (P.bounded_lf (P.shareOk op m _)))
  | store address value =>
    simp [leafPrice] at leaf; subst leaf
    simp only [compileHOLExact]
    rcases ha : compileExpHOLExact context (context.vmax + 1) live address with ⟨acode, av, anext, aout⟩
    rcases hv : compileExpHOLExact context anext aout value with ⟨vcode, vv, vnext, vout⟩
    obtain ⟨c1, s1, b1⟩ := P.exprOk context (context.vmax + 1) live address
    obtain ⟨c2, s2, b2⟩ := P.exprOk context anext aout value
    rw [ha] at s1 b1
    rw [hv] at s2 b2
    try dsimp only at s1 b1 s2 b2 ⊢
    have tail := LoopBoundedG.seq (P.bounded_lf (P.assignOk vnext vv))
      (LoopBoundedG.single (P.bounded_lf (P.storeOk av vnext)))
    have := P.A.codes_append acode _ c1 _ s1
      (P.A.codes_append vcode [.assign vnext vv, .store av vnext] c2 _ s2
        (by simpa only [loopNestedSeqHOL] using tail))
    try simp only [List.append_assoc] at this ⊢
    exact this.mono (by omega)
  | store32 address value =>
    simp [leafPrice] at leaf; subst leaf
    simp only [compileHOLExact]
    rcases ha : compileExpHOLExact context (context.vmax + 1) live address with ⟨acode, av, anext, aout⟩
    rcases hv : compileExpHOLExact context anext aout value with ⟨vcode, vv, vnext, vout⟩
    obtain ⟨c1, s1, b1⟩ := P.exprOk context (context.vmax + 1) live address
    obtain ⟨c2, s2, b2⟩ := P.exprOk context anext aout value
    rw [ha] at s1 b1
    rw [hv] at s2 b2
    try dsimp only at s1 b1 s2 b2 ⊢
    have tail := LoopBoundedG.seq (P.bounded_lf (P.assignOk vnext av))
      (LoopBoundedG.seq (P.bounded_lf (P.assignOk (vnext + 1) vv))
        (LoopBoundedG.single (P.bounded_lf (P.store32Ok vnext (vnext + 1)))))
    have := P.A.codes_append acode _ c1 _ s1
      (P.A.codes_append vcode [.assign vnext av, .assign (vnext + 1) vv, .store32 vnext (vnext + 1)] c2 _ s2
        (by simpa only [loopNestedSeqHOL] using tail))
    try simp only [List.append_assoc] at this ⊢
    exact this.mono (by omega)
  | storeByte address value =>
    simp [leafPrice] at leaf; subst leaf
    simp only [compileHOLExact]
    rcases ha : compileExpHOLExact context (context.vmax + 1) live address with ⟨acode, av, anext, aout⟩
    rcases hv : compileExpHOLExact context anext aout value with ⟨vcode, vv, vnext, vout⟩
    obtain ⟨c1, s1, b1⟩ := P.exprOk context (context.vmax + 1) live address
    obtain ⟨c2, s2, b2⟩ := P.exprOk context anext aout value
    rw [ha] at s1 b1
    rw [hv] at s2 b2
    try dsimp only at s1 b1 s2 b2 ⊢
    have tail := LoopBoundedG.seq (P.bounded_lf (P.assignOk vnext av))
      (LoopBoundedG.seq (P.bounded_lf (P.assignOk (vnext + 1) vv))
        (LoopBoundedG.single (P.bounded_lf (P.storeByteOk vnext (vnext + 1)))))
    have := P.A.codes_append acode _ c1 _ s1
      (P.A.codes_append vcode [.assign vnext av, .assign (vnext + 1) vv, .storeByte vnext (vnext + 1)] c2 _ s2
        (by simpa only [loopNestedSeqHOL] using tail))
    try simp only [List.append_assoc] at this ⊢
    exact this.mono (by omega)
  | «return» values =>
    simp [leafPrice] at leaf; subst leaf
    simp only [compileHOLExact]
    rcases hc : compileExpsHOLExact context (context.vmax + 1) live values with ⟨code, vs, next, out⟩
    obtain ⟨cost, supported, bound⟩ := P.listOk context (context.vmax + 1) live values
    rw [hc] at supported bound
    try dsimp only at supported bound ⊢
    obtain ⟨acost, asupported, abound⟩ := P.assign_codes (genTemps next vs.length) vs
    have := P.A.codes_append code _ cost _ supported
      (P.A.codes_append _ _ acost _ asupported
        (LoopBoundedG.single (P.bounded_lf (P.returnOk (genTemps next vs.length)))))
    try simp only [List.append_assoc] at this ⊢
    exact this.mono (by omega)
  | _ => simp [leafPrice] at leaf

end LoopPricingG

#print axioms LoopPricingG.leaf_compile
end InitECandidate.Runtime.FineCost
