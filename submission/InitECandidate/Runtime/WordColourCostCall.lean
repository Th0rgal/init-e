import InitECandidate.Runtime.WordColourCostBasis
import InitECandidate.Runtime.WordCallExecutionCost
import InitECandidate.Runtime.SSACallPermutationCost
import InitECandidate.Runtime.WordStackValueGlobalCost

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordAlloc
open Flapjack.WordSemStateFiniteExact Flapjack.WordSemStackEq
set_option maxHeartbeats 10000000

/-!
# Quantitative register colouring: calls

The call case of `evaluate_apply_colour` with executed work. Tail calls run the
unchanged callee on identical states. Returning calls push related frames;
the callee's cost is transported across the value-equal saved stack and the
permutation restitching (`word_stack_value_executed_cost`,
`ssa_permute_predicate_cost`), and the return/exception continuations use the
quantitative induction hypotheses at exactly the states of the semantic proof.
-/

section RetCont
variable {C F : Type} (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
  (n : List Nat) (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
  (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
  (envs : Spt (WordLocW 64) × Spt (WordLocW 64))

theorem retCont_flush (r : WordSemResult 64) (t : WordSemStateFiniteExact 64 C F)
    (hr : r = .timeOut ∨ r = .notEnoughSpace ∨ ∃ e, r = .finalFfi e) :
    retCont price n retCode l1 l2 handler envs (some r) t = 0 := by
  rcases hr with rfl | rfl | ⟨e, rfl⟩ <;> rfl

theorem retCont_result_pop (x : WordLocW 64) (ys : List (WordLocW 64))
    (t popped : WordSemStateFiniteExact 64 C F) (hg : ¬ (x ≠ .loc l1 l2 ∨ ys.length ≠ n.length))
    (hp : popEnv t = some popped) (hd : sptDomainEqUnion popped.locals envs.1 envs.2) :
    retCont price n retCode l1 l2 handler envs (some (.result x ys)) t =
      wordExecutionCost price retCode (setVars n ys popped) := by
  classical
  simp only [retCont, if_neg hg, hp, if_pos hd]

theorem retCont_exc_none (x y : WordLocW 64) (t : WordSemStateFiniteExact 64 C F) :
    retCont price n retCode l1 l2 none envs (some (.exception x y)) t = 0 := rfl

theorem retCont_exc_some (x y : WordLocW 64) (t : WordSemStateFiniteExact 64 C F)
    (v : Nat) (code : WordLangProgHOL (BitVec 64)) (h1 h2 : Nat)
    (hx : ¬ x ≠ .loc h1 h2) (hd : sptDomainEqUnion t.locals envs.1 envs.2) :
    retCont price n retCode l1 l2 (some (v, code, h1, h2)) envs (some (.exception x y)) t =
      wordExecutionCost price code (setVar v y t) := by
  classical
  simp only [retCont, if_neg hx, if_pos hd]

end RetCont

/-- A run that the source semantics rejects needs no target. -/
theorem colourCostPost_of_error {C F : Type} (price : WordLangProgHOL (BitVec 64) → Nat)
    (f : Nat → Nat) (prog : WordLangProgHOL (BitVec 64)) (live : NumSet)
    (lt : List (NumSet × NumSet)) (st cst : WordSemStateFiniteExact 64 C F)
    (error : (evaluate prog st).1 = some .error) :
    ColourCostPost price f prog live lt st cst :=
  ⟨st.permute, Or.inl error⟩

/-- Work of a returning call whose clock is exhausted at entry. -/
theorem ret_call_cost_timeout {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (n : List Nat) (names : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat) (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) (xs : List (WordLocW 64))
    (hg : getVars args s = some xs) (hbad : wordSemBadDestArgs dest args = false)
    (args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat)
    (hf : wordSemFindCode dest (.loc l1 l2 :: xs) s.code s.stackSize = some (args1, prog, ss))
    (hdc : ¬ (sptDomainEmpty names.1 ∨ ¬ n.Nodup)) (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (hce : wordSemCutEnvs names s.locals = some envs) (hz : s.clock = 0) :
    wordExecutionCost price (.call (some (n, names, retCode, l1, l2)) dest args handler) s =
      price (.call (some (n, names, retCode, l1, l2)) dest args handler) s := by
  rw [wordExecutionCost]
  simp only [hg, hbad, Bool.false_eq_true, if_false, wordSemAddRetLoc, hf, hdc, hce, dif_pos hz]

/-- Work of a tail call whose clock is exhausted at entry. -/
theorem tail_call_cost_timeout {C F : Type}
    (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (dest : Option Nat) (args : List Nat) (s : WordSemStateFiniteExact 64 C F) (xs : List (WordLocW 64))
    (hg : getVars args s = some xs) (hbad : wordSemBadDestArgs dest args = false)
    (args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat)
    (hf : wordSemFindCode dest xs s.code s.stackSize = some (args1, prog, ss)) (hz : s.clock = 0) :
    wordExecutionCost price (.call none dest args none) s = price (.call none dest args none) s := by
  rw [wordExecutionCost]
  simp only [hg, hbad, Bool.false_eq_true, if_false, wordSemAddRetLoc, hf, dif_pos hz]

/-- Tail calls: the same callee runs from the same state on both sides. -/
theorem colourCost_tail {C F : Type} (price : WordLangProgHOL (BitVec 64) → Nat)
    (invariant : ColourPriceInvariant price) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat)) :
    ColourCostGoal C F price (.call none dest args handler) := by
  classical
  rintro st cst f live lt ⟨hok, hs, hr⟩
  have ht := (evaluate_def_rebound (width := 64) (C := C) (F := F)
    ).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hargs : ∀ a, a ∈ args → sptDomain (getLive (.call none dest args handler) live lt) a := by
    intro a ha
    simp only [getLive]; exact (sptDomain_numsetIns _ _ _).mpr (Or.inr ha)
  cases hgv : getVars args st with
  | none =>
    apply colourCostPost_of_error
    rw [ht, hgv]
  | some xv =>
  have hgvC : getVars (args.map f) cst = some xv :=
    strongLocalsRelGetVars args xv f _ st cst ⟨hr, hargs, hgv⟩
  have hbadC : wordSemBadDestArgs dest (args.map f) = wordSemBadDestArgs dest args := by
    simp [wordSemBadDestArgs]
  by_cases hbad : wordSemBadDestArgs dest args = true
  · apply colourCostPost_of_error
    rw [ht, hgv]
    dsimp only
    rw [if_pos hbad]
  have hbadF : wordSemBadDestArgs dest args = false := by simpa using hbad
  have hcode : cst.code = st.code := wsrCode hs
  have hss : cst.stackSize = st.stackSize := by unfold wordStateEqRel at hs; exact hs.2.2.2.2.2.2.1
  have hclk : cst.clock = st.clock := wsrClock hs
  cases handler with
  | some hv =>
    apply colourCostPost_of_error
    rw [ht, hgv]
    dsimp only
    rw [if_neg hbad]
    split <;> rfl
  | none =>
  cases hfc : wordSemFindCode dest (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec 64) × Nat × Nat)) xv) st.code st.stackSize with
  | none =>
    apply colourCostPost_of_error
    rw [ht, hgv]
    dsimp only
    rw [if_neg hbad, hfc]
  | some fc =>
  obtain ⟨args1, prog, ss⟩ := fc
  have hfc' : wordSemFindCode dest xv st.code st.stackSize = some (args1, prog, ss) := hfc
  have hfcC : wordSemFindCode dest xv cst.code cst.stackSize = some (args1, prog, ss) := by
    rw [hcode, hss]; exact hfc'
  have targetCall : applyColour f (.call none dest args none : WordLangProgHOL (BitVec 64)) =
      .call none dest (args.map f) none := by
    rw [applyColour.eq_def]
  have hEq : evaluate (applyColour f (.call none dest args none)) cst =
      evaluate (.call none dest args none) {st with permute := cst.permute} := by
    simp only [applyColour]
    rw [ht cst, ht {st with permute := cst.permute}, hgvC, getVars_withPermute, hgv]
    dsimp only
    simp only [hbadC, hbad, Bool.false_eq_true, ↓reduceIte, hcode, hss, hfc, hclk]
    by_cases hz : st.clock = 0
    · simp only [hz, ↓reduceIte]
      congr 1
      conv => lhs; rw [← wsrEq hs]
      simp only [hz]
      try rfl
    · simp only [hz, ↓reduceIte]
      rw [callEnv_decClock_wsr hs]
  have hCost : wordExecutionCost (fun p _ => price p) (applyColour f (.call none dest args none)) cst ≤
      wordExecutionCost (fun p _ => price p) (.call none dest args none) {st with permute := cst.permute} := by
    have head := invariant f (.call none dest args none)
    rw [targetCall] at head ⊢
    have hbadC' : wordSemBadDestArgs dest (args.map f) = false := by rw [hbadC]; exact hbadF
    by_cases hz : st.clock = 0
    · rw [tail_call_cost_timeout _ dest (args.map f) cst xv hgvC hbadC' args1 prog ss hfcC (hclk.trans hz),
        tail_call_cost_timeout _ dest args {st with permute := cst.permute} xv
          (by rw [getVars_withPermute]; exact hgv) hbadF args1 prog ss hfc' hz]
      exact head
    · rw [tail_call_cost _ dest (args.map f) cst xv hgvC hbadC' args1 prog ss hfcC (by rw [hclk]; exact hz),
        tail_call_cost _ dest args {st with permute := cst.permute} xv
          (by rw [getVars_withPermute]; exact hgv) hbadF args1 prog ss hfc' hz,
        callEnv_decClock_wsr hs]
      exact Nat.add_le_add_right head _
  refine ⟨cst.permute, ?_⟩
  dsimp only
  by_cases herr : (evaluate (.call none dest args none) {st with permute := cst.permute}).1 = some .error
  · exact Or.inl herr
  refine Or.inr ⟨by rw [hEq], by rw [hEq]; exact wsrRefl _, ?_, hCost⟩
  rw [hEq]
  have hshape : ∀ r, (evaluate (.call none dest args none : WordLangProgHOL (BitVec 64))
      {st with permute := cst.permute}).1 = r → wordSemBadFunReturn r = true →
      r = some .error := by
    intro r hr0 hb
    rw [ht, getVars_withPermute, hgv] at hr0
    dsimp only at hr0
    rw [if_neg hbad, hfc] at hr0
    dsimp only at hr0
    by_cases hz : st.clock = 0
    · rw [if_pos hz] at hr0; subst hr0; simp [wordSemBadFunReturn] at hb
    · rw [if_neg hz] at hr0
      split at hr0
      · exact hr0.symm
      · rename_i hnb; rw [← hr0] at hb; exact absurd hb hnb
  generalize hE : (evaluate (.call none dest args none : WordLangProgHOL (BitVec 64))
    {st with permute := cst.permute}) = E at herr hshape ⊢
  rcases E with ⟨r, rst⟩
  dsimp only at herr hshape ⊢
  rcases r with _ | r
  · exact absurd (hshape none rfl rfl) (by simp)
  · cases r with
    | «break» k => exact absurd (hshape _ rfl rfl) (by simp)
    | «continue» k => exact absurd (hshape _ rfl rfl) (by simp)
    | _ => rfl

#print axioms colourCost_tail
end InitECandidate.Runtime.FineCost
