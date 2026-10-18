import InitECandidate.Runtime.SszSplitVarListAllocStage
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A word declaration passes clock facts and any locals-insensitive post facts. -/
theorem evaluate_dec_word_post {σ : Type} (s : PanSemStateFiniteExact 64 σ) (name : MlS) (e : ExpHOL 64)
    (body : ProgHOL 64) (w : BitVec 64) (K : Nat)
    (R : Option (PanSemResultExact 64) → PanSemStateFiniteExact 64 σ → Prop)
    (stable : ∀ r t L, R r t → R r {t with locals := L})
    (he : @evalHOLExact 64 σ _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a)) e = some (.val (.word w)))
    (h : s.clock ≤ (evaluateHOLFiniteState (setVarHOLFinite name (.val (.word w)) s) body).2.clock + K ∧
      (evaluateHOLFiniteState (setVarHOLFinite name (.val (.word w)) s) body).2.clock ≤ s.clock ∧
      R (evaluateHOLFiniteState (setVarHOLFinite name (.val (.word w)) s) body).1
        (evaluateHOLFiniteState (setVarHOLFinite name (.val (.word w)) s) body).2) :
    s.clock ≤ (evaluateHOLFiniteState s (.dec name .one e body)).2.clock + K ∧
      (evaluateHOLFiniteState s (.dec name .one e body)).2.clock ≤ s.clock ∧
      R (evaluateHOLFiniteState s (.dec name .one e body)).1 (evaluateHOLFiniteState s (.dec name .one e body)).2 := by
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  simp only [he, shapeOfHOLExact, shapeEqHOL, if_true]
  exact ⟨h.1, h.2.1, stable _ _ _ h.2.2⟩

/-- Accepted first offset: nonzero, 4-aligned, within len. -/
theorem andop_eq (x y : BitVec 64) : AndOp.and x y = x &&& y := rfl

def SszSplitFirstOK (len first : BitVec 64) : Prop := first ≠ 0 ∧ first &&& 3 = 0 ∧ ¬ len < first

theorem sszSplitFirstCheck_fail {σ : Type} (c : PanSemStateFiniteExact 64 σ) (len first : BitVec 64)
    (hl : c.locals.lookup (ofString "len") = some (.val (.word len)))
    (hf : c.locals.lookup (ofString "first") = some (.val (.word first)))
    (bad : first = 0 ∨ first &&& 3 ≠ 0 ∨ len < first) :
    evaluateHOLFiniteState c sszSplitFirstCheck =
      evaluateHOLFiniteState c (.call (some (none,none)) (ofString "ssz_fail") [.const 21]) := by
  unfold sszSplitFirstCheck
  have value : (if first = 0#64 then 1#64 else 0#64) ||| ((if first &&& 3#64 = 0#64 then 0#64 else 1#64) |||
      (if len < first then 1#64 else 0#64)) ≠ 0#64 := by
    intro h
    simp only [BitVec.or_eq_zero_iff] at h
    obtain ⟨h1, h2, h3⟩ := h
    rcases bad with b | b | b
    · have b' : first = 0#64 := b
      rw [if_pos b'] at h1; exact absurd h1 (by decide)
    · have b' : ¬ first &&& 3#64 = 0#64 := b
      rw [if_neg b'] at h2; exact absurd h2 (by decide)
    · rw [if_pos b] at h3; exact absurd h3 (by decide)
  simp [sszLocal, evaluateHOLFiniteState_ite, evalHOLExact, evalListHOLExact, hl, hf,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL, wordOpHOL, wordOp, valueIsWord, valueWord, orop_eq, andop_eq,
    Ne.symm value, -evaluateHOLFiniteState_call]

theorem sszSplitFirstCheck_pass {σ : Type} (c : PanSemStateFiniteExact 64 σ) (len first : BitVec 64)
    (hl : c.locals.lookup (ofString "len") = some (.val (.word len)))
    (hf : c.locals.lookup (ofString "first") = some (.val (.word first)))
    (ok : SszSplitFirstOK len first) :
    evaluateHOLFiniteState c sszSplitFirstCheck = (none, c) := by
  unfold sszSplitFirstCheck
  obtain ⟨o1, o2, o3⟩ := ok
  have o1' : ¬ first = 0#64 := o1
  have o2' : first &&& 3#64 = 0#64 := o2
  simp [sszLocal, evaluateHOLFiniteState_ite, evalHOLExact, evalListHOLExact, hl, hf, o1', o2', o3,
    Flapjack.Compiler.Encoders.Asm.wordCmpHOL, wordOpHOL, wordOp, valueIsWord, valueWord, orop_eq, andop_eq]

theorem evaluate_sszSplitFirstStage {σ : Type} (d : PanSemStateFiniteExact 64 σ)
    (p len first lim pointer : BitVec 64)
    (hp : d.locals.lookup (ofString "p") = some (.val (.word p)))
    (hlen : d.locals.lookup (ofString "len") = some (.val (.word len)))
    (hfirst : d.locals.lookup (ofString "first") = some (.val (.word first)))
    (hlim : d.locals.lookup (ofString "lim") = some (.val (.word lim)))
    (code : d.code = originalRuntimeCode)
    (heap : d.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (pointerBound : pointer.toNat ≤ 33806089496) (enough : 2 * (len.toNat / 4) + 2 ≤ d.clock) :
    d.clock ≤ (evaluateHOLFiniteState d sszSplitAfterFirst).2.clock + (2 * (len.toNat / 4) + 2) ∧
      (evaluateHOLFiniteState d sszSplitAfterFirst).2.clock ≤ d.clock ∧
      (evaluateHOLFiniteState d sszSplitAfterFirst).1 ≠ none ∧
      (evaluateHOLFiniteState d sszSplitAfterFirst).1 ≠ some .timeOut ∧
      (∀ v, (evaluateHOLFiniteState d sszSplitAfterFirst).1 = some (.returned v) →
        SszSplitFirstOK len first ∧ SszSplitAllocReturned d lim (first >>> (2 : Nat)) pointer v
          (evaluateHOLFiniteState d sszSplitAfterFirst).2) := by
  have c1n : ofString "count" ≠ ofString "p" := by decide_cbv
  have c2n : ofString "count" ≠ ofString "len" := by decide_cbv
  have c3n : ofString "count" ≠ ofString "first" := by decide_cbv
  have c4n : ofString "count" ≠ ofString "lim" := by decide_cbv
  unfold sszSplitAfterFirst
  rw [evaluateHOLFiniteState_seq_line780]
  by_cases bad : first = 0 ∨ first &&& 3 ≠ 0 ∨ len < first
  · rw [sszSplitFirstCheck_fail d len first hlen hfirst bad]
    obtain ⟨x, run, abnormal, c1, c2⟩ := sszFail_abnormal d 21 code (by omega)
    dsimp only
    rw [run]
    dsimp only
    exact ⟨by omega, c2, by rw [run]; simp, fun h => abnormal.2.1 (Option.some.inj (run.symm.trans h)),
      fun v h => absurd (Option.some.inj (run.symm.trans h)) (abnormal.2.2.2 v)⟩
  · have ok : SszSplitFirstOK len first :=
      ⟨fun h => bad (Or.inl h), Classical.byContradiction fun h' => bad (Or.inr (Or.inl h')),
        fun h => bad (Or.inr (Or.inr h))⟩
    rw [sszSplitFirstCheck_pass d len first hlen hfirst ok]
    dsimp only
    have he : @evalHOLExact 64 σ _ d.toExact (fun a => Classical.propDecidable (d.memaddrs a))
        (.shift .lsr (sszLocal "first") (.const 2)) = some (.val (.word (first >>> (2 : Nat)))) := by
      simp [sszLocal, evalHOLExact, hfirst, wordShiftHOL]
    have firstLe : first.toNat ≤ len.toNat := by have := ok.2.2; rw [BitVec.lt_def] at this; omega
    have cnt : (first >>> (2 : Nat)).toNat = first.toNat / 4 := by
      rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
    have cntLe : (first >>> (2 : Nat)).toNat ≤ len.toNat / 4 := by rw [cnt]; exact Nat.div_le_div_right firstLe
    have smallc : (first >>> (2 : Nat)).toNat < 2 ^ 62 := by rw [cnt]; have := first.isLt; omega
    apply evaluate_dec_word_post d (ofString "count") _ _ (first >>> (2 : Nat)) _
      (fun r t => r ≠ none ∧ r ≠ some .timeOut ∧ ∀ v, r = some (.returned v) →
        SszSplitFirstOK len first ∧ SszSplitAllocReturned d lim (first >>> (2 : Nat)) pointer v t)
      (fun _ _ _ h => h) he
    generalize hc : setVarHOLFinite (ofString "count") (.val (.word (first >>> (2 : Nat)))) d = c
    have up : ∀ k, k ≠ ofString "count" → c.locals.lookup k = d.locals.lookup k := by
      intro k hk; rw [← hc]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
    have cc : c.clock = d.clock := by rw [← hc]; rfl
    obtain ⟨s1, s2, s3, s4, s5⟩ := evaluate_sszSplitAllocStage c p len first (first >>> (2 : Nat)) lim pointer
      ((up _ c1n.symm).trans hp) ((up _ c2n.symm).trans hlen) ((up _ c3n.symm).trans hfirst)
      (by rw [← hc]; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]) ((up _ c4n.symm).trans hlim)
      (by rw [← hc]; exact code) (by rw [← hc]; exact heap) pointerBound smallc (by omega)
    refine ⟨by omega, by omega, s3, s4, fun v h => ⟨ok, ?_⟩⟩
    obtain ⟨x1, x2, x3, x4⟩ := s5 v h
    exact ⟨x1, x2, x3, x4.trans (by rw [← hc]; rfl)⟩

#print axioms evaluate_sszSplitFirstStage
end InitECandidate.Runtime
