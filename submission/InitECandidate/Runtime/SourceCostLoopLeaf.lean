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
      cost ≤ loopValuesWork values + values.length := by
  induction names generalizing values with
  | nil => exact ⟨0, by simp [List.zipWith, loopExpressionCodesWork], by omega⟩
  | cons name names ih =>
    cases values with
    | nil => exact ⟨0, by simp [List.zipWith, loopExpressionCodesWork], by omega⟩
    | cons value rest =>
      obtain ⟨cost, supported, bound⟩ := ih rest
      refine ⟨1 + loopValueWork value + cost, ?_, ?_⟩
      · simp [List.zipWith, loopExpressionCodesWork, loopExpressionCodeWork, supported]
      · simp only [loopValuesWork, List.length_cons]; omega

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

/-- Static Crep work of the non-recursive statements, as charged by `CrepWork`. -/
def crepLeafWork : CrepProgHOL 64 → Option Nat
  | .skip | .tick | .break _ | .continue _ | .raise _ | .extCall _ _ _ _ _ => some 1
  | .assign _ value | .storeGlob _ value | .shMem _ _ value => some (1 + crepNodeWork value)
  | .store address value | .store32 address value | .storeByte address value =>
      some (1 + crepNodeWork address + crepNodeWork value)
  | .return values => some (1 + crepListWork values + values.length)
  | .primitive names _ args => some (1 + names.length + args.length)
  | _ => none

theorem crepWork_leaf {σ : Type} {t : CrepSemHOLState 64 σ} {p : CrepProgHOL 64} {c : Nat}
    (leaf : crepLeafWork p = some c) : CrepWork t p c := by
  cases p <;> simp [crepLeafWork] at leaf <;> subst leaf
  all_goals first
    | exact CrepWork.skip t | exact CrepWork.tick t | exact CrepWork.breakStmt t _
    | exact CrepWork.continueStmt t _ | exact CrepWork.raise t _ | exact CrepWork.extCall t _ _ _ _ _
    | exact CrepWork.assign t _ _ | exact CrepWork.storeGlob t _ _ | exact CrepWork.shMem t _ _ _
    | exact CrepWork.store t _ _ | exact CrepWork.store32 t _ _ | exact CrepWork.storeByte t _ _
    | exact CrepWork.returnStmt t _ | exact CrepWork.primitive t _ _ _

/-- Every non-recursive Crep statement compiles to Loop code whose actual
execution from any state has work at most six times its Crep work. -/
theorem loopBounded_leaf_compile (context : CrepToLoopContextExact) (live : NumSet)
    (p : CrepProgHOL 64) (c : Nat) (leaf : crepLeafWork p = some c) :
    LoopBounded (compileHOLExact context live p) (6 * c) := by
  cases p with
  | skip =>
    simp [crepLeafWork] at leaf; subst leaf; rw [compileHOLExact]
    exact (loopBounded_leaf (program := .skip) (cost := 0) rfl).mono (by omega)
  | tick =>
    simp [crepLeafWork] at leaf; subst leaf; rw [compileHOLExact]
    exact (loopBounded_leaf (program := .tick) (cost := 1) rfl).mono (by omega)
  | «break» l =>
    simp [crepLeafWork] at leaf; subst leaf; rw [compileHOLExact]
    exact (loopBounded_leaf (program := .break l) (cost := 1) rfl).mono (by omega)
  | «continue» l =>
    simp [crepLeafWork] at leaf; subst leaf; rw [compileHOLExact]
    exact (loopBounded_leaf (program := .continue l) (cost := 1) rfl).mono (by omega)
  | raise e =>
    simp [crepLeafWork] at leaf; subst leaf
    simp only [compileHOLExact]
    exact (loopBounded_seq (loopBounded_leaf (program := .assign _ (.const e)) rfl)
      (loopBounded_leaf (program := .raise _) rfl)).mono (by simp [loopValueWork])
  | extCall f a b c d =>
    simp [crepLeafWork] at leaf; subst leaf
    simp only [compileHOLExact]
    split
    · exact (loopBounded_leaf (program := .ffi _ _ _ _ _ _) (cost := 1) rfl).mono (by omega)
    · exact (loopBounded_leaf (program := .skip) (cost := 0) rfl).mono (by omega)
  | primitive names op args =>
    simp [crepLeafWork] at leaf; subst leaf
    simp only [compileHOLExact]
    split
    · rename_i md ma hmd hma
      have l1 := opt_mmap_length_eq _ _ _ hmd
      have l2 := opt_mmap_length_eq _ _ _ hma
      exact (loopBounded_leaf (program := .primitive md op ma) rfl).mono (by
        first | omega | (simp only [loopWorkLeafCost] at *; omega))
    · exact (loopBounded_leaf (program := .skip) (cost := 0) rfl).mono (by omega)
  | assign name value =>
    simp [crepLeafWork] at leaf; subst leaf
    simp only [compileHOLExact]
    split
    · exact (loopBounded_leaf (program := .skip) (cost := 0) rfl).mono (by omega)
    · rename_i m _
      rcases hc : compileExpHOLExact context (context.vmax + 1) live value with
        ⟨code, v, next, out⟩
      obtain ⟨cost, supported, bound⟩ := crep_to_loop_local_work context (context.vmax + 1) live value
      rw [hc] at supported bound
      try dsimp only at supported bound ⊢
      exact (loopBounded_codes_append code _ cost _ supported
        (loopBounded_single (loopBounded_leaf (program := .assign m v) rfl))).mono (by
          first | omega | (simp only [loopWorkLeafCost] at *; omega))
  | storeGlob address value =>
    simp [crepLeafWork] at leaf; subst leaf
    simp only [compileHOLExact]
    rcases hc : compileExpHOLExact context (context.vmax + 1) live value with ⟨code, v, next, out⟩
    obtain ⟨cost, supported, bound⟩ := crep_to_loop_local_work context (context.vmax + 1) live value
    rw [hc] at supported bound
    try dsimp only at supported bound ⊢
    exact (loopBounded_codes_append code _ cost _ supported
      (loopBounded_single (loopBounded_leaf (program := .setGlobal address v) rfl))).mono (by
        first | omega | (simp only [loopWorkLeafCost] at *; omega))
  | shMem op name address =>
    simp [crepLeafWork] at leaf; subst leaf
    simp only [compileHOLExact]
    split
    · exact (loopBounded_leaf (program := .skip) (cost := 0) rfl).mono (by omega)
    · rename_i m _
      rcases hc : compileExpHOLExact context (context.vmax + 1) live address with
        ⟨code, v, next, out⟩
      obtain ⟨cost, supported, bound⟩ :=
        crep_to_loop_local_work context (context.vmax + 1) live address
      rw [hc] at supported bound
      try dsimp only at supported bound ⊢
      exact (loopBounded_codes_append code _ cost _ supported
        (loopBounded_single (loopBounded_leaf (program := .shMem op m v) rfl))).mono (by
          first | omega | (simp only [loopWorkLeafCost] at *; omega))
  | store address value =>
    simp [crepLeafWork] at leaf; subst leaf
    simp only [compileHOLExact]
    rcases ha : compileExpHOLExact context (context.vmax + 1) live address with
      ⟨acode, av, anext, aout⟩
    rcases hv : compileExpHOLExact context anext aout value with ⟨vcode, vv, vnext, vout⟩
    obtain ⟨c1, s1, b1⟩ := crep_to_loop_local_work context (context.vmax + 1) live address
    obtain ⟨c2, s2, b2⟩ := crep_to_loop_local_work context anext aout value
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
    simp [crepLeafWork] at leaf; subst leaf
    simp only [compileHOLExact]
    rcases ha : compileExpHOLExact context (context.vmax + 1) live address with
      ⟨acode, av, anext, aout⟩
    rcases hv : compileExpHOLExact context anext aout value with ⟨vcode, vv, vnext, vout⟩
    obtain ⟨c1, s1, b1⟩ := crep_to_loop_local_work context (context.vmax + 1) live address
    obtain ⟨c2, s2, b2⟩ := crep_to_loop_local_work context anext aout value
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
    simp [crepLeafWork] at leaf; subst leaf
    simp only [compileHOLExact]
    rcases ha : compileExpHOLExact context (context.vmax + 1) live address with
      ⟨acode, av, anext, aout⟩
    rcases hv : compileExpHOLExact context anext aout value with ⟨vcode, vv, vnext, vout⟩
    obtain ⟨c1, s1, b1⟩ := crep_to_loop_local_work context (context.vmax + 1) live address
    obtain ⟨c2, s2, b2⟩ := crep_to_loop_local_work context anext aout value
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
    simp [crepLeafWork] at leaf; subst leaf
    simp only [compileHOLExact]
    rcases hc : compileExpsHOLExact context (context.vmax + 1) live values with
      ⟨code, vs, next, out⟩
    obtain ⟨cost, supported, bound⟩ := crep_to_loop_list_work context (context.vmax + 1) live values
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
  | _ => simp [crepLeafWork] at leaf

#print axioms loopBounded_leaf_compile
end InitECandidate.Runtime.FineCost
