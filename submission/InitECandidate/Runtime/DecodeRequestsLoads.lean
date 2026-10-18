import InitECandidate.Runtime.DecodeRequestsCounts
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem req_eval_load_one_word {σ : Type} (st : PanSemStateExact 64 σ) [DecidablePred st.memaddrs] (a : ExpHOL 64)
    (v : ValueHOL 64) (h : evalHOLExact st (.load .one a) = some v) : ∃ w : BitVec 64, v = .val (.word w) := by
  rw [evalHOLExact] at h
  split at h
  · split at h
    · simp only [memLoadHOLExact] at h
      split at h
      · simp only [Option.some.injEq] at h
        subst h
        cases hm : st.memory _ with
        | word w => exact ⟨w, rfl⟩
      · simp at h
    · simp at h
  · simp at h

/-- A word declaration whose initializer only yields words passes any bound of its body. -/
theorem reqWordDec_bounded {σ : Type} (P Q : PanSemStateFiniteExact 64 σ → Prop) (name : MlS) (e : ExpHOL 64)
    (body : ProgHOL 64) (T : Nat)
    (hval : ∀ t : PanSemStateFiniteExact 64 σ, ∀ v,
      @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e = some v →
      ∃ w : BitVec 64, v = .val (.word w))
    (hbody : ∀ t w, P t → Q (setVarHOLFinite name (.val (.word w)) t))
    (bodyB : ReqBounded Q body T) : ReqBounded P (.dec name .one e body) T := by
  intro t pt en
  rw [evaluateHOLFiniteState_dec_total]
  dsimp only
  cases h : @evalHOLExact 64 σ _ t.toExact (fun a => Classical.propDecidable (t.memaddrs a)) e with
  | none => simp only [h]; exact ⟨by omega, Nat.le_refl _, by simp⟩
  | some v =>
    obtain ⟨w, rfl⟩ := hval t _ h
    simp only [h, shapeOfHOLExact, shapeEqHOL, if_true]
    exact bodyB _ (hbody t w pt) en

def ReqLoadsPre {σ : Type} (t : PanSemStateFiniteExact 64 σ) : Prop :=
  t.code = originalRuntimeCode ∧ ∃ L : BitVec 64, t.locals.lookup (ofString "len") = some (.val (.word L))

theorem reqLoads_bounded {σ : Type} : ReqBounded (σ := σ) ReqLoadsPre reqLoads 335 := by
  have loadWord : ∀ (a : ExpHOL 64) (t : PanSemStateFiniteExact 64 σ) v,
      @evalHOLExact 64 σ _ t.toExact (fun x => Classical.propDecidable (t.memaddrs x)) (.load .one a) = some v →
      ∃ w : BitVec 64, v = .val (.word w) := fun a t v h => @req_eval_load_one_word σ t.toExact (fun x => Classical.propDecidable (t.memaddrs x)) a v h
  let up (t : PanSemStateFiniteExact 64 σ) (n : String) (w : BitVec 64) (k : MlS) (hk : k ≠ ofString n) :
      (setVarHOLFinite (ofString n) (.val (.word w)) t).locals.lookup k = t.locals.lookup k := by
    simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE, Ne.symm hk]
  have own : ∀ (t : PanSemStateFiniteExact 64 σ) (n : String) (w : BitVec 64),
      (setVarHOLFinite (ofString n) (.val (.word w)) t).locals.lookup (ofString n) = some (.val (.word w)) := by
    intro t n w; simp [setVarHOLFinite, HolFiniteMapExact.lookup_update, FUPDATE]
  unfold reqLoads
  apply reqWordDec_bounded ReqLoadsPre
    (fun t => t.code = originalRuntimeCode ∧ ∃ L O0 : BitVec 64, t.locals.lookup (ofString "len") = some (.val (.word L)) ∧
      t.locals.lookup (ofString "o0") = some (.val (.word O0))) _ _ _ _ (loadWord _)
  · rintro t w ⟨c, L, hL⟩
    exact ⟨c, L, w, (up t "o0" w _ (by decide_cbv)).trans hL, own t "o0" w⟩
  apply reqWordDec_bounded _
    (fun t => t.code = originalRuntimeCode ∧ ∃ L O0 O1 : BitVec 64, t.locals.lookup (ofString "len") = some (.val (.word L)) ∧
      t.locals.lookup (ofString "o0") = some (.val (.word O0)) ∧ t.locals.lookup (ofString "o1") = some (.val (.word O1)))
    _ _ _ _ (loadWord _)
  · rintro t w ⟨c, L, O0, hL, h0⟩
    exact ⟨c, L, O0, w, (up t "o1" w _ (by decide_cbv)).trans hL, (up t "o1" w _ (by decide_cbv)).trans h0, own t "o1" w⟩
  apply reqWordDec_bounded _
    (fun t => t.code = originalRuntimeCode ∧ ∃ L O0 O1 O2 : BitVec 64,
      t.locals.lookup (ofString "len") = some (.val (.word L)) ∧ t.locals.lookup (ofString "o0") = some (.val (.word O0)) ∧
      t.locals.lookup (ofString "o1") = some (.val (.word O1)) ∧ t.locals.lookup (ofString "o2") = some (.val (.word O2)))
    _ _ _ _ (loadWord _)
  · rintro t w ⟨c, L, O0, O1, hL, h0, h1⟩
    exact ⟨c, L, O0, O1, w, (up t "o2" w _ (by decide_cbv)).trans hL, (up t "o2" w _ (by decide_cbv)).trans h0,
      (up t "o2" w _ (by decide_cbv)).trans h1, own t "o2" w⟩
  apply reqWordDec_bounded _
    (fun t => t.code = originalRuntimeCode ∧ ∃ L O0 O1 O2 O3 : BitVec 64,
      t.locals.lookup (ofString "len") = some (.val (.word L)) ∧ t.locals.lookup (ofString "o0") = some (.val (.word O0)) ∧
      t.locals.lookup (ofString "o1") = some (.val (.word O1)) ∧ t.locals.lookup (ofString "o2") = some (.val (.word O2)) ∧
      t.locals.lookup (ofString "o3") = some (.val (.word O3)))
    _ _ _ _ (loadWord _)
  · rintro t w ⟨c, L, O0, O1, O2, hL, h0, h1, h2⟩
    exact ⟨c, L, O0, O1, O2, w, (up t "o3" w _ (by decide_cbv)).trans hL, (up t "o3" w _ (by decide_cbv)).trans h0,
      (up t "o3" w _ (by decide_cbv)).trans h1, (up t "o3" w _ (by decide_cbv)).trans h2, own t "o3" w⟩
  apply reqWordDec_bounded _ ReqCountsPre _ _ _ _ (loadWord _)
  · rintro t w ⟨c, L, O0, O1, O2, O3, hL, h0, h1, h2, h3⟩
    exact ⟨c, L, O0, O1, O2, O3, w, (up t "o4" w _ (by decide_cbv)).trans hL, (up t "o4" w _ (by decide_cbv)).trans h0,
      (up t "o4" w _ (by decide_cbv)).trans h1, (up t "o4" w _ (by decide_cbv)).trans h2,
      (up t "o4" w _ (by decide_cbv)).trans h3, own t "o4" w⟩
  exact reqCounts_bounded

#print axioms reqLoads_bounded
end InitECandidate.Runtime
