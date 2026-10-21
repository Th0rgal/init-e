import InitECandidate.Runtime.SourceCostLoopCode
import InitECandidate.Runtime.SourceCostCrepWork
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

theorem loopBounded_codes_append : ∀ (codes rest : List (HolLoopProg 64)) (c b : Nat),
    loopExpressionCodesWork codes = some c → LoopBounded (loopNestedSeqHOL rest) b →
    LoopBounded (loopNestedSeqHOL (codes ++ rest)) (c + b)
  | [], rest, c, b, h, tail => by
    simp [loopExpressionCodesWork] at h; subst h; simpa using tail
  | head :: tail, rest, c, b, h, restBounded => by
    simp only [loopExpressionCodesWork] at h
    cases ha : loopExpressionCodeWork head <;> cases hb : loopExpressionCodesWork tail <;>
      simp_all
    rename_i a t
    subst h
    have := loopBounded_seq (loopBounded_of_codeWork head a ha)
      (loopBounded_codes_append tail rest t b hb restBounded)
    simpa [loopNestedSeqHOL, Nat.add_assoc] using this

theorem loopBounded_single {statement : HolLoopProg 64} {c : Nat}
    (bounded : LoopBounded statement c) : LoopBounded (loopNestedSeqHOL [statement]) c := by
  have := loopBounded_seq bounded (loopBounded_leaf (program := .skip) (cost := 0) rfl)
  simpa [loopNestedSeqHOL] using this

theorem assign_codes_work (names : List Nat) (values : List (HolLoopExp 64)) :
    ∃ cost, loopExpressionCodesWork (names.zipWith HolLoopProg.assign values) = some cost ∧
      cost ≤ loopNativeValues values := by
  induction names generalizing values with
  | nil => exact ⟨0, by simp [List.zipWith, loopExpressionCodesWork], by omega⟩
  | cons name names ih =>
    cases values with
    | nil => exact ⟨0, by simp [List.zipWith, loopExpressionCodesWork], by omega⟩
    | cons value rest =>
      obtain ⟨cost, supported, bound⟩ := ih rest
      refine ⟨loopNativeValue value + cost, ?_, ?_⟩
      · simp [List.zipWith, loopExpressionCodesWork, loopExpressionCodeWork, supported]
      · simp only [loopNativeValues, List.length_cons]; omega

theorem loopCompileExps_length (context : CrepToLoopContextExact) :
    ∀ (es : List (CrepExpHOL 64)) (tmp : Nat) (live : NumSet),
      (compileExpsHOLExact context tmp live es).2.1.length = es.length
  | [], _, _ => by simp [compileExpsHOLExact]
  | e :: es, tmp, live => by
    rcases hA : compileExpHOLExact context tmp live e with ⟨c, v, n, o⟩
    rcases hB : compileExpsHOLExact context n o es with ⟨c', vs, n', o'⟩
    have := loopCompileExps_length context es n o
    rw [hB] at this
    simp only [compileExpsHOLExact, hA, hB, List.length_cons]
    simp only [] at this
    omega

/-- A Loop pricing of Crep work: an expression price and an argument-list
price that dominate the native compiled Loop code work, a statement unit, a
raise/primitive unit and a call unit. The list price also pays the native
argument move (39) of each argument. -/
structure LoopPricing where
  price : CrepExpHOL 64 → Nat
  priceList : List (CrepExpHOL 64) → Nat
  unit : Nat
  prim : Nat
  call : Nat
  ret : Nat
  exprOk : ∀ (context : CrepToLoopContextExact) (tmp : Nat) (live : NumSet) (e : CrepExpHOL 64),
    ∃ cost, loopExpressionCodesWork (compileExpHOLExact context tmp live e).1 = some cost ∧
      cost + loopNativeValue (compileExpHOLExact context tmp live e).2.1 ≤ price e
  listOk : ∀ (context : CrepToLoopContextExact) (tmp : Nat) (live : NumSet) (es : List (CrepExpHOL 64)),
    ∃ cost, loopExpressionCodesWork (compileExpsHOLExact context tmp live es).1 = some cost ∧
      cost + loopNativeValues (compileExpsHOLExact context tmp live es).2.1 +
        39 * (compileExpsHOLExact context tmp live es).2.1.length ≤ priceList es
  unitOk : 37 ≤ unit
  primOk : 85 ≤ prim
  callOk : 196 ≤ call
  retOk : 49 ≤ ret

/-- Crep work priced by a Loop pricing. -/
abbrev CrepWorkL (P : LoopPricing) {σ : Type} := @CrepWorkP P.price P.priceList P.unit P.prim P.call P.ret σ

/-- Static priced work of the non-recursive statements, as charged by `CrepWorkL`. -/
def crepLeafPrice (P : LoopPricing) : CrepProgHOL 64 → Option Nat
  | .skip => some 0
  | .tick | .break _ | .continue _ | .extCall _ _ _ _ _ => some P.unit
  | .raise _ => some (P.prim + 1)
  | .assign _ value => some (P.price value)
  | .storeGlob _ value | .shMem _ _ value => some (P.unit + P.price value)
  | .store address value | .store32 address value | .storeByte address value =>
      some (P.unit + P.price address + P.price value)
  | .return values => some (P.unit + P.priceList values + values.length)
  | .primitive names _ args => some (P.prim + names.length + args.length)
  | _ => none

theorem crepWork_leaf {σ : Type} (P : LoopPricing) {t : CrepSemHOLState 64 σ} {p : CrepProgHOL 64}
    {c : Nat} (leaf : crepLeafPrice P p = some c) : CrepWorkL P t p c := by
  cases p <;> simp [crepLeafPrice] at leaf <;> subst leaf
  all_goals first
    | exact CrepWorkP.skip t | exact CrepWorkP.tick t | exact CrepWorkP.breakStmt t _
    | exact CrepWorkP.continueStmt t _ | exact CrepWorkP.raise t _ | exact CrepWorkP.extCall t _ _ _ _ _
    | exact CrepWorkP.assign t _ _ | exact CrepWorkP.storeGlob t _ _ | exact CrepWorkP.shMem t _ _ _
    | exact CrepWorkP.store t _ _ | exact CrepWorkP.store32 t _ _ | exact CrepWorkP.storeByte t _ _
    | exact CrepWorkP.returnStmt t _ | exact CrepWorkP.primitive t _ _ _

theorem pricing_list_work (P : LoopPricing) (context : CrepToLoopContextExact) (tmp : Nat) (live : NumSet)
    (es : List (CrepExpHOL 64)) :
    let compiled := compileExpsHOLExact context tmp live es
    ∃ cost, loopExpressionCodesWork compiled.1 = some cost ∧
      cost + loopNativeValues compiled.2.1 + 39 * compiled.2.1.length ≤ P.priceList es := by
  obtain ⟨cost, h, b⟩ := P.listOk context tmp live es
  exact ⟨cost, h, by omega⟩

/-- Every non-recursive Crep statement compiles to Loop code whose actual
execution from any state has work at most its priced Crep work. -/
theorem loopBounded_leaf_compile (P : LoopPricing) (context : CrepToLoopContextExact) (live : NumSet)
    (p : CrepProgHOL 64) (c : Nat) (leaf : crepLeafPrice P p = some c) :
    LoopBounded (compileHOLExact context live p) c := by
  have unit := P.unitOk
  have prim := P.primOk
  cases p with
  | skip =>
    simp [crepLeafPrice] at leaf; subst leaf; rw [compileHOLExact]
    exact (loopBounded_leaf (program := .skip) (cost := 0) rfl).mono (by omega)
  | tick =>
    simp [crepLeafPrice] at leaf; subst leaf; rw [compileHOLExact]
    exact (loopBounded_leaf (program := .tick) (cost := 7) rfl).mono (by omega)
  | «break» l =>
    simp [crepLeafPrice] at leaf; subst leaf; rw [compileHOLExact]
    exact (loopBounded_leaf (program := .break l) (cost := 7) rfl).mono (by omega)
  | «continue» l =>
    simp [crepLeafPrice] at leaf; subst leaf; rw [compileHOLExact]
    exact (loopBounded_leaf (program := .continue l) (cost := 7) rfl).mono (by omega)
  | raise e =>
    simp [crepLeafPrice] at leaf; subst leaf
    simp only [compileHOLExact]
    exact (loopBounded_seq (loopBounded_leaf (program := .assign _ (.const e)) rfl)
      (loopBounded_leaf (program := .raise _) rfl)).mono (by simp only [loopWorkLeafCost, loopNativeValue] at *; omega)
  | extCall f a b c d =>
    simp [crepLeafPrice] at leaf; subst leaf
    simp only [compileHOLExact]
    split
    · exact (loopBounded_leaf (program := .ffi _ _ _ _ _ _) (cost := 25) rfl).mono (by omega)
    · exact (loopBounded_leaf (program := .skip) (cost := 0) rfl).mono (by omega)
  | primitive names op args =>
    simp [crepLeafPrice] at leaf; subst leaf
    simp only [compileHOLExact]
    split
    · rename_i md ma hmd hma
      have l1 := opt_mmap_length_eq _ _ _ hmd
      have l2 := opt_mmap_length_eq _ _ _ hma
      exact (loopBounded_leaf (program := .primitive md op ma) rfl).mono (by
        first | omega | (simp only [loopWorkLeafCost] at *; omega))
    · exact (loopBounded_leaf (program := .skip) (cost := 0) rfl).mono (by omega)
  | assign name value =>
    simp [crepLeafPrice] at leaf; subst leaf
    simp only [compileHOLExact]
    split
    · exact (loopBounded_leaf (program := .skip) (cost := 0) rfl).mono (by omega)
    · rename_i m _
      rcases hc : compileExpHOLExact context (context.vmax + 1) live value with
        ⟨code, v, next, out⟩
      obtain ⟨cost, supported, bound⟩ := P.exprOk context (context.vmax + 1) live value
      rw [hc] at supported bound
      try dsimp only at supported bound ⊢
      exact (loopBounded_codes_append code _ cost _ supported
        (loopBounded_single (loopBounded_leaf (program := .assign m v) rfl))).mono (by
          first | omega | (simp only [loopWorkLeafCost] at *; omega))
  | storeGlob address value =>
    simp [crepLeafPrice] at leaf; subst leaf
    simp only [compileHOLExact]
    rcases hc : compileExpHOLExact context (context.vmax + 1) live value with ⟨code, v, next, out⟩
    obtain ⟨cost, supported, bound⟩ := P.exprOk context (context.vmax + 1) live value
    rw [hc] at supported bound
    try dsimp only at supported bound ⊢
    exact (loopBounded_codes_append code _ cost _ supported
      (loopBounded_single (loopBounded_leaf (program := .setGlobal address v) rfl))).mono (by
        first | omega | (simp only [loopWorkLeafCost] at *; omega))
  | shMem op name address =>
    simp [crepLeafPrice] at leaf; subst leaf
    simp only [compileHOLExact]
    split
    · exact (loopBounded_leaf (program := .skip) (cost := 0) rfl).mono (by omega)
    · rename_i m _
      rcases hc : compileExpHOLExact context (context.vmax + 1) live address with
        ⟨code, v, next, out⟩
      obtain ⟨cost, supported, bound⟩ :=
        P.exprOk context (context.vmax + 1) live address
      rw [hc] at supported bound
      try dsimp only at supported bound ⊢
      exact (loopBounded_codes_append code _ cost _ supported
        (loopBounded_single (loopBounded_leaf (program := .shMem op m v) rfl))).mono (by
          first | omega | (simp only [loopWorkLeafCost] at *; omega))
  | store address value =>
    simp [crepLeafPrice] at leaf; subst leaf
    simp only [compileHOLExact]
    rcases ha : compileExpHOLExact context (context.vmax + 1) live address with
      ⟨acode, av, anext, aout⟩
    rcases hv : compileExpHOLExact context anext aout value with ⟨vcode, vv, vnext, vout⟩
    obtain ⟨c1, s1, b1⟩ := P.exprOk context (context.vmax + 1) live address
    obtain ⟨c2, s2, b2⟩ := P.exprOk context anext aout value
    rw [ha] at s1 b1
    rw [hv] at s2 b2
    try dsimp only at s1 b1 s2 b2 ⊢
    have tail := loopBounded_seq (loopBounded_leaf (program := .assign vnext vv) rfl)
      (loopBounded_single (loopBounded_leaf (program := .store av vnext) rfl))
    have := loopBounded_codes_append acode _ c1 _ s1
      (loopBounded_codes_append vcode [.assign vnext vv, .store av vnext] c2 _ s2
        (by simpa only [loopNestedSeqHOL] using tail))
    try simp only [List.append_assoc] at this ⊢
    exact this.mono (by first | omega | (simp only [loopWorkLeafCost] at *; omega))
  | store32 address value =>
    simp [crepLeafPrice] at leaf; subst leaf
    simp only [compileHOLExact]
    rcases ha : compileExpHOLExact context (context.vmax + 1) live address with
      ⟨acode, av, anext, aout⟩
    rcases hv : compileExpHOLExact context anext aout value with ⟨vcode, vv, vnext, vout⟩
    obtain ⟨c1, s1, b1⟩ := P.exprOk context (context.vmax + 1) live address
    obtain ⟨c2, s2, b2⟩ := P.exprOk context anext aout value
    rw [ha] at s1 b1
    rw [hv] at s2 b2
    try dsimp only at s1 b1 s2 b2 ⊢
    have tail := loopBounded_seq (loopBounded_leaf (program := .assign vnext av) rfl)
      (loopBounded_seq (loopBounded_leaf (program := .assign (vnext + 1) vv) rfl)
        (loopBounded_single (loopBounded_leaf (program := .store32 vnext (vnext + 1)) rfl)))
    have := loopBounded_codes_append acode _ c1 _ s1
      (loopBounded_codes_append vcode
        [.assign vnext av, .assign (vnext + 1) vv, .store32 vnext (vnext + 1)] c2 _ s2
        (by simpa only [loopNestedSeqHOL] using tail))
    try simp only [List.append_assoc] at this ⊢
    exact this.mono (by first | omega | (simp only [loopWorkLeafCost] at *; omega))
  | storeByte address value =>
    simp [crepLeafPrice] at leaf; subst leaf
    simp only [compileHOLExact]
    rcases ha : compileExpHOLExact context (context.vmax + 1) live address with
      ⟨acode, av, anext, aout⟩
    rcases hv : compileExpHOLExact context anext aout value with ⟨vcode, vv, vnext, vout⟩
    obtain ⟨c1, s1, b1⟩ := P.exprOk context (context.vmax + 1) live address
    obtain ⟨c2, s2, b2⟩ := P.exprOk context anext aout value
    rw [ha] at s1 b1
    rw [hv] at s2 b2
    try dsimp only at s1 b1 s2 b2 ⊢
    have tail := loopBounded_seq (loopBounded_leaf (program := .assign vnext av) rfl)
      (loopBounded_seq (loopBounded_leaf (program := .assign (vnext + 1) vv) rfl)
        (loopBounded_single (loopBounded_leaf (program := .storeByte vnext (vnext + 1)) rfl)))
    have := loopBounded_codes_append acode _ c1 _ s1
      (loopBounded_codes_append vcode
        [.assign vnext av, .assign (vnext + 1) vv, .storeByte vnext (vnext + 1)] c2 _ s2
        (by simpa only [loopNestedSeqHOL] using tail))
    try simp only [List.append_assoc] at this ⊢
    exact this.mono (by first | omega | (simp only [loopWorkLeafCost] at *; omega))
  | «return» values =>
    simp [crepLeafPrice] at leaf; subst leaf
    simp only [compileHOLExact]
    rcases hc : compileExpsHOLExact context (context.vmax + 1) live values with
      ⟨code, vs, next, out⟩
    obtain ⟨cost, supported, bound⟩ := pricing_list_work P context (context.vmax + 1) live values
    rw [hc] at supported bound
    try dsimp only at supported bound ⊢
    obtain ⟨acost, asupported, abound⟩ := assign_codes_work (genTemps next vs.length) vs
    have := loopBounded_codes_append code _ cost _ supported
      (loopBounded_codes_append _ _ acost _ asupported
        (loopBounded_single (loopBounded_leaf (program := .return (genTemps next vs.length)) rfl)))
    try simp only [List.append_assoc] at this ⊢
    have lengths : vs.length ≤ values.length := by
      have := loopCompileExps_length context values (context.vmax + 1) live
      rw [hc] at this; simp only [] at this; omega
    refine this.mono ?_
    simp only [loopWorkLeafCost, genTemps, List.length_map, List.length_range] at *
    omega
  | _ => simp [crepLeafPrice] at leaf

#print axioms loopBounded_leaf_compile
end InitECandidate.Runtime.FineCost
