import InitECandidate.Runtime.CrepSelPrice
import InitECandidate.Runtime.SourceCostLoopLeaf
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend

/-! Selector-priced execution bounds for the Loop code of non-recursive Crep
statements: the selector analogue of `loopBounded_leaf_compile`. -/

theorem selExpCost_le_fW (e : WordLangExpHOL (BitVec 64)) : selExpCost e ≤ fW e := by
  have h1 := iselCost_flatten (WordInst.ExecutablePullExp.pullExpExecutable e)
  have h2 := fW_pull e
  simp only [selExpCost]; omega

theorem isel_share_lineBound (c : Compiler.Encoders.Asm.AsmConfigExact 64) (temp : Nat) (op : WordMemOp) (v : Nat)
    (e : WordLangExpHOL (BitVec 64)) :
    ∃ k, lineBound preAllocLeafBudget (WordInst.instSelectExecutable c temp (.shareInst op v e)) = some k ∧
      k ≤ selExpCost e + 13 := by
  have leaf : ∀ a, lineBound preAllocLeafBudget (.shareInst op v a) = some 13 := by
    intro a; simp [lineBound, isLeafProg, preAllocLeafBudget, WordToStack.refinedWordStackLeafBudget]
  simp only [WordInst.instSelectExecutable, selExpCost]
  split
  · rename_i exp' w heq
    split
    · obtain ⟨k, hk, hle⟩ := isel_lineBound c temp temp exp'
      refine ⟨k + 13, by rw [lineBound, hk, leaf], ?_⟩
      rw [heq, iselCost_op2]; omega
    · obtain ⟨k, hk, hle⟩ := isel_lineBound c temp temp (.op .add [exp', .const w])
      exact ⟨k + 13, by rw [lineBound, heq, hk, leaf], by rw [heq]; omega⟩
  · obtain ⟨k, hk, hle⟩ := isel_lineBound c temp temp
      (WordInst.flattenExp (WordInst.ExecutablePullExp.pullExpExecutable e))
    exact ⟨k + 13, by rw [lineBound, hk, leaf], by omega⟩

theorem iselX_le_of {c : Compiler.Encoders.Asm.AsmConfigExact 64} {p : WordLangProgHOL (BitVec 64)} {k b : Nat}
    (h : lineBound preAllocLeafBudget (WordInst.instSelectExecutable c 0 p) = some k) (le : k ≤ b) :
    iselX c p ≤ b := by simp only [iselX, h, Option.getD_some]; exact le

theorem leafPL_setGlobal (c : Compiler.Encoders.Asm.AsmConfigExact 64) (T1 T2 : SiteTable) (a : BitVec 5)
    (v : HolLoopExp 64) : ∃ k, leafPL c T1 T2 (.setGlobal a v) = some k ∧ k ≤ fL v + 12 := by
  refine ⟨iselX c (.set (.temp a) (LoopToWord.compExpHOL .ln v)), ?_, ?_⟩
  · simp [leafPL, loopWorkLeafCost, LoopToWord.compHOL, lineBound, isLeafProg, leafNodeB, isExprStmt, nodeEnv,
      siteKey]
  · obtain ⟨k, hk, hle⟩ := isel_set_lineBound c 0 (.temp a) (LoopToWord.compExpHOL .ln v)
    have := selExpCost_le_fW (LoopToWord.compExpHOL .ln v)
    rw [fW_compExp] at this
    exact iselX_le_of hk (by omega)

theorem leafPL_store (c : Compiler.Encoders.Asm.AsmConfigExact 64) (T1 T2 : SiteTable) (e : HolLoopExp 64)
    (v : Nat) : ∃ k, leafPL c T1 T2 (.store e v) = some k ∧ k ≤ fL e + 24 := by
  refine ⟨iselX c (.store (LoopToWord.compExpHOL .ln e) (LoopToWord.findVarHOL .ln v)), ?_, ?_⟩
  · simp [leafPL, loopWorkLeafCost, LoopToWord.compHOL, lineBound, isLeafProg, leafNodeB, isExprStmt, nodeEnv,
      siteKey]
  · obtain ⟨k, hk, hle⟩ := isel_store_lineBound c 0 (LoopToWord.findVarHOL .ln v) (LoopToWord.compExpHOL .ln e)
    have := selExpCost_le_fW (LoopToWord.compExpHOL .ln e)
    rw [fW_compExp] at this
    exact iselX_le_of hk (by omega)

theorem leafPL_shMem (c : Compiler.Encoders.Asm.AsmConfigExact 64) (T1 T2 : SiteTable) (op : WordMemOp)
    (n : Nat) (e : HolLoopExp 64) : ∃ k, leafPL c T1 T2 (.shMem op n e) = some k ∧ k ≤ fL e + 13 := by
  refine ⟨iselX c (.shareInst op (LoopToWord.findVarHOL .ln n) (LoopToWord.compExpHOL .ln e)), ?_, ?_⟩
  · simp [leafPL, loopWorkLeafCost, LoopToWord.compHOL, lineBound, isLeafProg, leafNodeB, isExprStmt, nodeEnv,
      siteKey]
  · obtain ⟨k, hk, hle⟩ := isel_share_lineBound c 0 op (LoopToWord.findVarHOL .ln n) (LoopToWord.compExpHOL .ln e)
    have := selExpCost_le_fW (LoopToWord.compExpHOL .ln e)
    rw [fW_compExp] at this
    exact iselX_le_of hk (by omega)

#print axioms leafPL_shMem

theorem leafPL_simple (c : Compiler.Encoders.Asm.AsmConfigExact 64) :
    leafPL c wsT1 wsT2 .skip = some 0 ∧ leafPL c wsT1 wsT2 .tick = some 6 ∧
    (∀ l, leafPL c wsT1 wsT2 (.break l) = some 2) ∧ (∀ l, leafPL c wsT1 wsT2 (.continue l) = some 0) ∧
    (∀ e, leafPL c wsT1 wsT2 (.raise e) = some 63) ∧ (∀ vs, leafPL c wsT1 wsT2 (.return vs) = some 15) ∧
    (∀ a v, leafPL c wsT1 wsT2 (.store32 a v) = some 24) ∧ (∀ a v, leafPL c wsT1 wsT2 (.storeByte a v) = some 24) := by
  refine ⟨?_, ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ _ => ?_, fun _ _ => ?_⟩ <;>
  simp [leafPL, loopWorkLeafCost, LoopToWord.compHOL, lineBound, isLeafProg, leafNodeB, isExprStmt, nodeEnv,
    siteKey, preAllocLeafBudget, WordToStack.refinedWordStackLeafBudget,
    Compiler.Encoders.Asm.HolInst.ofWordLangInst, WordToStack.refinedNativeInstructionPrice]

/-- The selector-derived price of an FFI leaf, with its site-kind envelope. -/
def ffiSel : Nat := 25 + 24 * (kindMax wsT2 3 + kindMax wsT1 3)

theorem leafPL_ffi (c : Compiler.Encoders.Asm.AsmConfigExact 64) (f : Basis.Pure.MlString.MlString)
    (a b d e : Nat) (live : NumSet) : leafPL c wsT1 wsT2 (.ffi f a b d e live) = some ffiSel := by
  simp [leafPL, loopWorkLeafCost, LoopToWord.compHOL, lineBound, isLeafProg, leafNodeB, isExprStmt, nodeEnv,
    siteKey, preAllocLeafBudget, WordToStack.refinedWordStackLeafBudget, ffiSel]

theorem leafPL_primitive (c : Compiler.Encoders.Asm.AsmConfigExact 64) (ds : List Nat) (op : PrimOp)
    (as : List Nat) : ∃ k, leafPL c wsT1 wsT2 (.primitive ds op as) = some k ∧ k ≤ 111 := by
  cases op
  rcases ds with _ | ⟨d1, _ | ⟨d2, _ | ⟨d3, ds⟩⟩⟩ <;>
    rcases as with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, as⟩⟩⟩⟩ <;>
    simp [leafPL, loopWorkLeafCost, LoopToWord.compHOL, lineBound, isLeafProg, leafNodeB, isExprStmt, nodeEnv,
      siteKey, preAllocLeafBudget, WordToStack.refinedWordStackLeafBudget,
      Compiler.Encoders.Asm.HolInst.ofWordLangInst, Compiler.Encoders.Asm.HolArith.ofWordLangArith,
      WordToStack.refinedNativeInstructionPrice]
  have h1 := iselX_assign_le c 1 (.var (LoopToWord.findVarHOL .ln a3))
  have h2 := iselX_assign_le c (LoopToWord.findVarHOL .ln d2) (.var 1)
  have h3 := iselX_assign_le c (LoopToWord.findVarHOL .ln d1) (.var 3)
  simp only [fW] at h1 h2 h3
  omega

theorem LoopBoundedS.mono {c : Compiler.Encoders.Asm.AsmConfigExact 64} {p : HolLoopProg 64} {a b : Nat}
    (h : LoopBoundedS c p a) (le : a ≤ b) : LoopBoundedS c p b := by
  intro F f s; obtain ⟨w, work, bound⟩ := h F f s; exact ⟨w, work, by omega⟩

theorem loopBoundedS_codes_append (c : Compiler.Encoders.Asm.AsmConfigExact 64) :
    ∀ (codes rest : List (HolLoopProg 64)) (k b : Nat), selCodesWork codes = some k →
      LoopBoundedS c (loopNestedSeqHOL rest) b → LoopBoundedS c (loopNestedSeqHOL (codes ++ rest)) (k + b)
  | [], rest, k, b, h, tail => by
    simp [selCodesWork] at h; subst h; simpa using tail
  | head :: tail, rest, k, b, h, restBounded => by
    simp only [selCodesWork] at h
    cases ha : selCodeWork head <;> cases hb : selCodesWork tail <;> simp_all
    rename_i x y
    subst h
    have := loopBoundedS_seq (selCodeWork_bounded c head x ha)
      (loopBoundedS_codes_append c tail rest y b hb restBounded)
    simpa [loopNestedSeqHOL, Nat.add_assoc] using this

theorem loopBoundedS_single {c : Compiler.Encoders.Asm.AsmConfigExact 64} {p : HolLoopProg 64} {k : Nat}
    (h : LoopBoundedS c p k) : LoopBoundedS c (loopNestedSeqHOL [p]) k := by
  have := loopBoundedS_seq h (loopBoundedS_leaf (leafPL_simple c).1 (Nat.le_refl 0))
  simpa [loopNestedSeqHOL] using this

theorem loopBoundedS_leafPL {c : Compiler.Encoders.Asm.AsmConfigExact 64} {p : HolLoopProg 64} {b : Nat}
    (h : ∃ k, leafPL c wsT1 wsT2 p = some k ∧ k ≤ b) : LoopBoundedS c p b := by
  obtain ⟨k, hk, le⟩ := h; exact loopBoundedS_leaf hk le

#print axioms loopBoundedS_codes_append

theorem sel_assign_codes (names : List Nat) (values : List (HolLoopExp 64)) :
    ∃ cost, selCodesWork (names.zipWith HolLoopProg.assign values) = some cost ∧ cost ≤ fLs values := by
  induction names generalizing values with
  | nil => exact ⟨0, by simp [List.zipWith, selCodesWork], by omega⟩
  | cons name names ih =>
    cases values with
    | nil => exact ⟨0, by simp [List.zipWith, selCodesWork], by omega⟩
    | cons value rest =>
      obtain ⟨cost, supported, bound⟩ := ih rest
      refine ⟨fL value + cost, ?_, ?_⟩
      · simp [List.zipWith, selCodesWork, selCodeWork, supported]
      · simp only [fLs]; omega

/-- Selector-derived price of a non-recursive Crep statement. -/
def selCrepLeafPrice : CrepProgHOL 64 → Option Nat
  | .skip => some 0
  | .tick => some 6
  | .break _ => some 2
  | .continue _ => some 0
  | .extCall _ _ _ _ _ => some ffiSel
  | .raise _ => some 87
  | .assign _ value => some (selNodePrice value)
  | .storeGlob _ value => some (selNodePrice value + 12)
  | .shMem _ _ address => some (selNodePrice address + 13)
  | .store address value => some (selNodePrice address + selNodePrice value + 24)
  | .store32 address value | .storeByte address value =>
      some (selNodePrice address + selNodePrice value + 24)
  | .return values => some (selPriceList values + 15)
  | .primitive _ _ _ => some 111
  | _ => none

/-- Every non-recursive Crep statement compiles to Loop code whose actual
execution, in any calling function and from any state, has selector-priced
work at most its selector-derived price. -/
theorem loopBoundedS_leaf_compile (c : Compiler.Encoders.Asm.AsmConfigExact 64)
    (context : CrepToLoopContextExact) (live : NumSet) (p : CrepProgHOL 64) (k : Nat)
    (leaf : selCrepLeafPrice p = some k) : LoopBoundedS c (compileHOLExact context live p) k := by
  have simple := leafPL_simple c
  cases p with
  | skip =>
    simp [selCrepLeafPrice] at leaf; subst leaf; rw [compileHOLExact]
    exact loopBoundedS_leaf simple.1 (Nat.le_refl _)
  | tick =>
    simp [selCrepLeafPrice] at leaf; subst leaf; rw [compileHOLExact]
    exact loopBoundedS_leaf simple.2.1 (Nat.le_refl _)
  | «break» l =>
    simp [selCrepLeafPrice] at leaf; subst leaf; rw [compileHOLExact]
    exact loopBoundedS_leaf (simple.2.2.1 l) (Nat.le_refl _)
  | «continue» l =>
    simp [selCrepLeafPrice] at leaf; subst leaf; rw [compileHOLExact]
    exact loopBoundedS_leaf (simple.2.2.2.1 l) (Nat.le_refl _)
  | raise e =>
    simp [selCrepLeafPrice] at leaf; subst leaf
    simp only [compileHOLExact]
    obtain ⟨k1, h1, b1⟩ := leafPL_assign c wsT1 wsT2 _ (.const e)
    exact (loopBoundedS_seq (loopBoundedS_leaf h1 (Nat.le_refl _))
      (loopBoundedS_leaf (simple.2.2.2.2.1 _) (Nat.le_refl _))).mono (by simp only [fL] at b1; omega)
  | extCall f a b c' d =>
    simp [selCrepLeafPrice] at leaf; subst leaf
    simp only [compileHOLExact]
    split
    · exact loopBoundedS_leaf (leafPL_ffi c _ _ _ _ _ _) (Nat.le_refl _)
    · exact loopBoundedS_leaf simple.1 (Nat.zero_le _)
  | primitive names op args =>
    simp [selCrepLeafPrice] at leaf; subst leaf
    simp only [compileHOLExact]
    split
    · exact loopBoundedS_leafPL (leafPL_primitive c _ _ _)
    · exact loopBoundedS_leaf simple.1 (Nat.zero_le _)
  | assign name value =>
    simp [selCrepLeafPrice] at leaf; subst leaf
    simp only [compileHOLExact]
    split
    · exact loopBoundedS_leaf simple.1 (Nat.zero_le _)
    · rename_i m _
      rcases hc : compileExpHOLExact context (context.vmax + 1) live value with ⟨code, v, next, out⟩
      obtain ⟨cost, supported, bound⟩ := crep_to_loop_sel_work context (context.vmax + 1) live value
      rw [hc] at supported bound
      try dsimp only at supported bound ⊢
      exact (loopBoundedS_codes_append c code _ cost _ supported
        (loopBoundedS_single (loopBoundedS_leafPL (leafPL_assign c wsT1 wsT2 m v)))).mono (by omega)
  | storeGlob address value =>
    simp [selCrepLeafPrice] at leaf; subst leaf
    simp only [compileHOLExact]
    rcases hc : compileExpHOLExact context (context.vmax + 1) live value with ⟨code, v, next, out⟩
    obtain ⟨cost, supported, bound⟩ := crep_to_loop_sel_work context (context.vmax + 1) live value
    rw [hc] at supported bound
    try dsimp only at supported bound ⊢
    exact (loopBoundedS_codes_append c code _ cost _ supported
      (loopBoundedS_single (loopBoundedS_leafPL (leafPL_setGlobal c wsT1 wsT2 address v)))).mono (by omega)
  | shMem op name address =>
    simp [selCrepLeafPrice] at leaf; subst leaf
    simp only [compileHOLExact]
    split
    · exact loopBoundedS_leaf simple.1 (Nat.zero_le _)
    · rename_i m _
      rcases hc : compileExpHOLExact context (context.vmax + 1) live address with ⟨code, v, next, out⟩
      obtain ⟨cost, supported, bound⟩ := crep_to_loop_sel_work context (context.vmax + 1) live address
      rw [hc] at supported bound
      try dsimp only at supported bound ⊢
      exact (loopBoundedS_codes_append c code _ cost _ supported
        (loopBoundedS_single (loopBoundedS_leafPL (leafPL_shMem c wsT1 wsT2 op m v)))).mono (by omega)
  | store address value =>
    simp [selCrepLeafPrice] at leaf; subst leaf
    simp only [compileHOLExact]
    rcases ha : compileExpHOLExact context (context.vmax + 1) live address with ⟨acode, av, anext, aout⟩
    rcases hv : compileExpHOLExact context anext aout value with ⟨vcode, vv, vnext, vout⟩
    obtain ⟨c1, s1, b1⟩ := crep_to_loop_sel_work context (context.vmax + 1) live address
    obtain ⟨c2, s2, b2⟩ := crep_to_loop_sel_work context anext aout value
    rw [ha] at s1 b1
    rw [hv] at s2 b2
    try dsimp only at s1 b1 s2 b2 ⊢
    have tail := loopBoundedS_seq (loopBoundedS_leafPL (leafPL_assign c wsT1 wsT2 vnext vv))
      (loopBoundedS_single (loopBoundedS_leafPL (leafPL_store c wsT1 wsT2 av vnext)))
    have := loopBoundedS_codes_append c acode _ c1 _ s1
      (loopBoundedS_codes_append c vcode [.assign vnext vv, .store av vnext] c2 _ s2
        (by simpa only [loopNestedSeqHOL] using tail))
    try simp only [List.append_assoc] at this ⊢
    exact this.mono (by omega)
  | store32 address value =>
    simp [selCrepLeafPrice] at leaf; subst leaf
    simp only [compileHOLExact]
    rcases ha : compileExpHOLExact context (context.vmax + 1) live address with ⟨acode, av, anext, aout⟩
    rcases hv : compileExpHOLExact context anext aout value with ⟨vcode, vv, vnext, vout⟩
    obtain ⟨c1, s1, b1⟩ := crep_to_loop_sel_work context (context.vmax + 1) live address
    obtain ⟨c2, s2, b2⟩ := crep_to_loop_sel_work context anext aout value
    rw [ha] at s1 b1
    rw [hv] at s2 b2
    try dsimp only at s1 b1 s2 b2 ⊢
    have tail := loopBoundedS_seq (loopBoundedS_leafPL (leafPL_assign c wsT1 wsT2 vnext av))
      (loopBoundedS_seq (loopBoundedS_leafPL (leafPL_assign c wsT1 wsT2 (vnext + 1) vv))
        (loopBoundedS_single (loopBoundedS_leaf (simple.2.2.2.2.2.2.1 vnext (vnext + 1)) (Nat.le_refl _))))
    have := loopBoundedS_codes_append c acode _ c1 _ s1
      (loopBoundedS_codes_append c vcode
        [.assign vnext av, .assign (vnext + 1) vv, .store32 vnext (vnext + 1)] c2 _ s2
        (by simpa only [loopNestedSeqHOL] using tail))
    try simp only [List.append_assoc] at this ⊢
    exact this.mono (by omega)
  | storeByte address value =>
    simp [selCrepLeafPrice] at leaf; subst leaf
    simp only [compileHOLExact]
    rcases ha : compileExpHOLExact context (context.vmax + 1) live address with ⟨acode, av, anext, aout⟩
    rcases hv : compileExpHOLExact context anext aout value with ⟨vcode, vv, vnext, vout⟩
    obtain ⟨c1, s1, b1⟩ := crep_to_loop_sel_work context (context.vmax + 1) live address
    obtain ⟨c2, s2, b2⟩ := crep_to_loop_sel_work context anext aout value
    rw [ha] at s1 b1
    rw [hv] at s2 b2
    try dsimp only at s1 b1 s2 b2 ⊢
    have tail := loopBoundedS_seq (loopBoundedS_leafPL (leafPL_assign c wsT1 wsT2 vnext av))
      (loopBoundedS_seq (loopBoundedS_leafPL (leafPL_assign c wsT1 wsT2 (vnext + 1) vv))
        (loopBoundedS_single (loopBoundedS_leaf (simple.2.2.2.2.2.2.2 vnext (vnext + 1)) (Nat.le_refl _))))
    have := loopBoundedS_codes_append c acode _ c1 _ s1
      (loopBoundedS_codes_append c vcode
        [.assign vnext av, .assign (vnext + 1) vv, .storeByte vnext (vnext + 1)] c2 _ s2
        (by simpa only [loopNestedSeqHOL] using tail))
    try simp only [List.append_assoc] at this ⊢
    exact this.mono (by omega)
  | «return» values =>
    simp [selCrepLeafPrice] at leaf; subst leaf
    simp only [compileHOLExact]
    rcases hc : compileExpsHOLExact context (context.vmax + 1) live values with ⟨code, vs, next, out⟩
    obtain ⟨cost, supported, bound⟩ := crep_to_loop_sel_list_work context (context.vmax + 1) live values
    rw [hc] at supported bound
    try dsimp only at supported bound ⊢
    obtain ⟨acost, asupported, abound⟩ := sel_assign_codes (genTemps next vs.length) vs
    have := loopBoundedS_codes_append c code _ cost _ supported
      (loopBoundedS_codes_append c _ _ acost _ asupported
        (loopBoundedS_single (loopBoundedS_leaf (simple.2.2.2.2.2.1 (genTemps next vs.length)) (Nat.le_refl _))))
    try simp only [List.append_assoc] at this ⊢
    exact this.mono (by omega)
  | _ => simp [selCrepLeafPrice] at leaf

#print axioms loopBoundedS_leaf_compile
end InitECandidate.Runtime.FineCost
