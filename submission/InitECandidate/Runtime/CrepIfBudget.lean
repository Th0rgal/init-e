import InitECandidate.Runtime.CrepCallBudget
namespace InitECandidate.Runtime
open Flapjack
open Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- Bounds the selected branch execution and its one live-set cut, retaining
all original compiler relations. Adapted from original ncompile_correct[If]. -/
theorem crep_if_bounded_step {width : Nat} [NeZero width] {σ : Type} :
    ∀ (e : CrepExpHOL width) (c1 c2 : CrepProgHOL width) (v1 : CrepSemHOLState width σ) (branchBudget : Nat),
      (∀ w, evalCrepSemHOLExp v1 e = some (.word w) →
        BoundedCrepPropertyAt (if w ≠ 0 then c1 else c2) v1 branchBudget) →
    ∀ (res : Option (CrepResultHOLExact width)) (s1 : CrepSemHOLState width σ)
      (t : LoopSemStateFiniteExact width σ) (ctxt : CrepToLoopContextExact) (l : NumSet),
      evalCrepSemHOLProgExact v1 (.ite e c1 c2) = (res, s1) ∧ res ≠ some .error ∧
        crepToLoopStateRelExact v1 t ∧
        crepToLoopMemRelHOLExact v1.memory t.memory v1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact v1.globals t.globals ∧
        crepToLoopCodeRelExact ctxt v1.code t.code ∧
        crepToLoopLocalsRelExact ctxt l v1.locals t.locals →
      ∃ (ck : Nat), ck ≤ crepExprFuel e + branchBudget + 1 ∧ ∃ (res1 : Option (LoopSemStateFiniteExact.LoopResultExact width))
        (t1 : LoopSemStateFiniteExact width σ),
        LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l (.ite e c1 c2))
            { t with clock := t.clock + ck } = (res1, t1) ∧
        crepToLoopStateRelExact s1 t1 ∧
        crepToLoopMemRelHOLExact s1.memory t1.memory s1.memaddrs ∧
        crepToLoopGlobalsRelHOLExact s1.globals t1.globals ∧
        crepToLoopCodeRelExact ctxt s1.code t1.code ∧
        res1 = resultToLoop res ∧
        localsResultRel ctxt l res s1 t1 := by
  intro e c1 c2 v1 branchBudget ih res s1 t ctxt l ⟨he, hne, hs, hm, hg, hc, hl⟩
  rw [evalCrepSemHOLProgExact_eq_evaluate_def] at he
  simp only at he
  cases hev : evalCrepSemHOLExp v1 e with
  | none =>
    simp only [hev, Prod.mk.injEq] at he
    exact absurd he.1.symm hne
  | some x =>
  cases x with
  | word w =>
  simp only [hev] at he
  rcases hC : compileExpHOLExact ctxt (ctxt.vmax + 1) l e with ⟨np, le, tmp, nl⟩
  obtain ⟨ck, exprSmall, st, h1, h1v, h1s, h1m, h1g, h1c, h1l⟩ :=
    crep_expression_fuel_bounded v1 e (.word w) t ctxt (ctxt.vmax + 1) l np le tmp nl
      ⟨hev, hs, hm, hg, hc, hl, hC, Nat.lt_succ_self _⟩
  obtain ⟨hokA, htA, hlA⟩ := compile_exp_out_rel ctxt (ctxt.vmax + 1) l e np le tmp nl hC
  -- `st with locals := insert tmp (Word w) st.locals` satisfies `locals_rel ctxt l`
  have hl' : crepToLoopLocalsRelExact ctxt l v1.locals
      (LoopSemStateFiniteExact.setVar tmp (.word w) st).locals := by
    refine ⟨h1l.1, h1l.2.1, fun k hk => ?_, fun vn val hval => ?_⟩
    · have hnl : sptDomain nl k := hlA ▸ cut_sets_union_domain_subset _ l hokA k hk
      exact (sptMem_sptInsert k tmp _ _).mpr (Or.inr (h1l.2.2.1 k hnl))
    · obtain ⟨n, hn1, hn2, _⟩ := hl.2.2.2 vn val hval
      obtain ⟨n', hn1', _, hn3'⟩ := h1l.2.2.2 vn val hval
      have hnn : n' = n := Option.some.inj (hn1'.symm.trans hn1)
      subst hnn
      have hle := h1l.2.1 vn n' hn1'
      refine ⟨n', hn1', hn2, ?_⟩
      simp only [LoopSemStateFiniteExact.setVar, sptLookup_sptInsert]
      rw [if_neg (by omega)]
      exact hn3'
  obtain ⟨ck', branchSmall, res1, t1, h2, h2s, h2m, h2g, h2c, h2r, h2l⟩ :=
    ih w hev res s1 (LoopSemStateFiniteExact.setVar tmp (.word w) st) ctxt l
      he hne h1s h1m h1g h1c hl'
  have hcomp : compileHOLExact ctxt l (.ite e c1 c2) =
      loopNestedSeqHOL (np ++
        [.assign tmp le,
         .ite .notEqual tmp (.imm (0 : BitVec width))
           (compileHOLExact ctxt l c1) (compileHOLExact ctxt l c2) l]) := by
    rw [compileHOLExact, hC]
  rw [hcomp]
  -- the `Assign tmp le; If NotEqual tmp (Imm 0w) ...` tail from any clock extension
  have htail : ∀ k, LoopSemStateFiniteExact.evaluate
      (loopNestedSeqHOL
        [.assign tmp le,
         .ite .notEqual tmp (.imm (0 : BitVec width))
           (compileHOLExact ctxt l c1) (compileHOLExact ctxt l c2) l])
      { st with clock := st.clock + k } =
      LoopSemStateFiniteExact.cutRes l
        (LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l (if w ≠ 0 then c1 else c2))
          { LoopSemStateFiniteExact.setVar tmp (.word w) st with clock := st.clock + k }) := by
    intro k
    have hle : LoopSemStateFiniteExact.eval { st with clock := st.clock + k } le =
        some (.word w) := by
      rw [LoopSemStateFiniteExact.eval_upd_clock_eq]; simpa [wlabWlocExact] using h1v
    simp only [loopNestedSeqHOL, LoopSemStateFiniteExact.evaluate_seq]
    simp only [LoopSemStateFiniteExact.evaluate, hle]
    simp only [LoopSemStateFiniteExact.setVar, sptLookup_sptInsert, if_true,
      LoopSemStateFiniteExact.getVarImm, Compiler.Encoders.Asm.wordCmpHOL]
    by_cases hw : w = 0
    · simp only [hw, beq_self_eq_true, Bool.not_true, Bool.false_eq_true, if_false,
        ne_eq, not_true_eq_false]
      split <;> rename_i h <;> exact h.symm
    · have hb : (w == 0) = false := by simpa using hw
      simp only [hb, Bool.not_false, if_true, ne_eq, hw, not_false_eq_true]
      split <;> rename_i h <;> exact h.symm
  have h1k : ∀ k, LoopSemStateFiniteExact.evaluate (loopNestedSeqHOL np)
      { t with clock := t.clock + (ck + k) } = (none, { st with clock := st.clock + k }) := by
    intro k
    have := LoopSemStateFiniteExact.evaluate_add_clock_eq _ _ _ _ k h1 (by simp)
    simpa [Nat.add_assoc] using this
  have h2' : LoopSemStateFiniteExact.evaluate (compileHOLExact ctxt l (if w ≠ 0 then c1 else c2))
      { LoopSemStateFiniteExact.setVar tmp (.word w) st with clock := st.clock + ck' } =
        (res1, t1) := h2
  cases res with
  | none =>
    have hr1 : res1 = none := by simpa [resultToLoop] using h2r
    subst hr1
    have h2l' : crepToLoopLocalsRelExact ctxt l s1.locals t1.locals := h2l
    have h2k : LoopSemStateFiniteExact.evaluate
        (compileHOLExact ctxt l (if w ≠ 0 then c1 else c2))
        { LoopSemStateFiniteExact.setVar tmp (.word w) st with clock := st.clock + (ck' + 1) } =
          (none, { t1 with clock := t1.clock + 1 }) := by
      have := LoopSemStateFiniteExact.evaluate_add_clock_eq _ _ _ _ 1 h2' (by simp)
      simpa [Nat.add_assoc] using this
    have hsub : LoopSemStateFiniteExact.sptSubsetLive l t1.locals := h2l'.2.2.1
    have hcut : LoopSemStateFiniteExact.cutRes l (none, { t1 with clock := t1.clock + 1 }) =
        (none, { t1 with locals := sptInter t1.locals l }) := by
      rw [LoopSemStateFiniteExact.cutRes]
      simp only
      rw [LoopSemStateFiniteExact.cutState_of_subset l { t1 with clock := t1.clock + 1 } hsub]
      simp [LoopSemStateFiniteExact.decClock]
    refine ⟨ck + (ck' + 1), by omega, none, { t1 with locals := sptInter t1.locals l }, ?_, h2s, h2m,
      h2g, h2c, rfl, ?_⟩
    · rw [LoopSemStateFiniteExact.evaluate_nested_seq_append_none np _ _ _ (h1k (ck' + 1)),
        htail, h2k, hcut]
    · refine ⟨h2l'.1, h2l'.2.1, fun k hk => ?_, fun vn val hval => ?_⟩
      · have hk' : (sptLookup k l).isSome := hk
        show (sptLookup k (sptInter t1.locals l)).isSome
        rw [sptLookup_sptInter, if_pos hk']
        exact hsub k hk
      · obtain ⟨n, hn1, hn2, hn3⟩ := h2l'.2.2.2 vn val hval
        have hnl : (sptLookup n l).isSome := hn2
        refine ⟨n, hn1, hn2, ?_⟩
        show sptLookup n (sptInter t1.locals l) = _
        rw [sptLookup_sptInter, if_pos hnl]
        exact hn3
  | some r =>
    obtain ⟨x, hx⟩ : ∃ x, res1 = some x := by
      cases r <;> simp only [resultToLoop] at h2r <;> exact ⟨_, h2r⟩
    refine ⟨ck + ck', by omega, res1, t1, ?_, h2s, h2m, h2g, h2c, h2r, h2l⟩
    rw [LoopSemStateFiniteExact.evaluate_nested_seq_append_none np _ _ _ (h1k ck'), htail, h2', hx]
    rfl



#print axioms crep_if_bounded_step
end InitECandidate.Runtime
