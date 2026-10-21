import InitECandidate.Runtime.WordColourCostCall

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordAlloc
open Flapjack.WordSemStateFiniteExact Flapjack.WordSemStackEq
set_option maxHeartbeats 20000000

/-- Returning calls, with or without an exception handler. The source oracle is
`ppPerm root suffix`: the root orders the pushed frame as in the semantic
proof, and the suffix is chosen for the callee so that the continuation
predicate holds while the callee's executed cost is unchanged. -/
theorem colourCost_returning {C F : Type} (price : WordLangProgHOL (BitVec 64) → Nat)
    (invariant : ColourPriceInvariant price)
    (n : List Nat) (n1 n2 : Spt Unit) (rh : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (ihRet : ColourCostGoal C F price rh)
    (ihHandler : ∀ v h l1 l2, handler = some (v, h, l1, l2) → ColourCostGoal C F price h) :
    ColourCostGoal C F price (.call (some (n, (n1, n2), rh, l1, l2)) dest args handler) := by
  classical
  rintro st cst f live lt ⟨hok, hs, hr⟩
  have ht := (evaluate_def_rebound (width := 64) (C := C) (F := F)
    ).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hargs : ∀ a, a ∈ args →
      sptDomain (getLive (.call (some (n, (n1, n2), rh, l1, l2)) dest args handler) live lt) a := by
    intro a ha
    simp only [getLive]
    exact (sptDomain_uni _ _ _).mpr (Or.inr ((sptDomain_numsetIns _ _ _).mpr (Or.inr ha)))
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
  have hok' := hok
  unfold colouringOk at hok'
  obtain ⟨hinjA, hinjN, hokRh, hokH⟩ := hok'
  simp only [getLive] at hr
  have hmA : ∀ k, (sptDomain n1 k ∨ sptDomain n2 k) →
      sptDomain (sptUnion (sptUnion n2 n1) (numsetListInsert args .ln)) k := by
    intro k hk
    rw [sptDomain_uni, sptDomain_uni]
    rcases hk with hk | hk
    · exact Or.inl (Or.inr hk)
    · exact Or.inl (Or.inl hk)
  have hmR : ∀ k, (sptDomain n1 k ∨ sptDomain n2 k) →
      sptDomain (sptUnion (sptUnion n1 n2) (numsetListInsert args .ln)) k := by
    intro k hk
    rw [sptDomain_uni, sptDomain_uni]
    exact Or.inl hk
  have inj12 : ∀ a b, (sptDomain n1 a ∨ sptDomain n2 a) → (sptDomain n1 b ∨ sptDomain n2 b) →
      f a = f b → a = b := fun a b ha hb => hinjA a b (hmA a ha) (hmA b hb)
  have inj1 : ∀ a b, sptDomain n1 a → sptDomain n1 b → f a = f b → a = b :=
    fun a b ha hb => inj12 a b (Or.inl ha) (Or.inl hb)
  have inj2 : ∀ a b, sptDomain n2 a → sptDomain n2 b → f a = f b → a = b :=
    fun a b ha hb => inj12 a b (Or.inr ha) (Or.inr hb)
  have rel1 : strongLocalsRel f (sptDomain n1) st.locals cst.locals :=
    fun k v ⟨hk, h⟩ => hr k v ⟨hmR k (Or.inl hk), h⟩
  have rel2 : strongLocalsRel f (sptDomain n2) st.locals cst.locals :=
    fun k v ⟨hk, h⟩ => hr k v ⟨hmR k (Or.inr hk), h⟩
  cases hfc : wordSemFindCode dest (wordSemAddRetLoc (some (n, (n1, n2), rh, l1, l2)) xv)
      st.code st.stackSize with
  | none =>
    apply colourCostPost_of_error
    rw [ht, hgv]
    dsimp only
    rw [if_neg hbad, hfc]
  | some fc =>
  obtain ⟨args1, prog, ss⟩ := fc
  have hfc' : wordSemFindCode dest (.loc l1 l2 :: xv) st.code st.stackSize =
      some (args1, prog, ss) := hfc
  by_cases hg : sptDomainEmpty n1 ∨ ¬ n.Nodup
  · apply colourCostPost_of_error
    rw [ht, hgv]
    dsimp only
    rw [if_neg hbad, hfc]
    dsimp only
    rw [if_pos hg]
  have hgC : ¬ (sptDomainEmpty (applyNummapsKey f (n1, n2)).1 ∨ ¬ (n.map f).Nodup) := by
    intro h
    apply hg
    rcases h with h | h
    · left
      intro k hk
      apply h (f k)
      show sptDomain (applyNummapsKey f (n1, n2)).1 (f k)
      rw [(nummapsToNummap f (n1, n2)).1, applyNummapKeyDomain]
      exact ⟨k, hk, rfl⟩
    · right
      intro hnd
      apply h
      refine nodup_map_of_injOn f n (fun a b ha hb hab => hinjN a b ?_ ?_ hab) hnd
      · exact (sptDomain_numsetIns _ _ _).mpr (Or.inr ha)
      · exact (sptDomain_numsetIns _ _ _).mpr (Or.inr hb)
  cases hce : wordSemCutEnvs (n1, n2) st.locals with
  | none =>
    apply colourCostPost_of_error
    rw [ht, hgv]
    dsimp only
    rw [if_neg hbad, hfc]
    dsimp only
    rw [if_neg hg, hce]
  | some xs =>
  obtain ⟨x1, x2⟩ := xs
  obtain ⟨y1, y2, hceC, hdy1, hdy2, hr1, hr2, hi1, hi2, hdx1, hdx2⟩ :=
    cutEnvsLemma n1 n2 st.locals cst.locals x1 x2 f ⟨inj1, inj2, hce, rel1, rel2⟩
  have hfcC : wordSemFindCode dest (wordSemAddRetLoc (some (n.map f, applyNummapsKey f (n1, n2),
      applyColour f rh, l1, l2)) xv) cst.code cst.stackSize = some (args1, prog, ss) := by
    rw [hcode, hss]; exact hfc
  have hfcC' : wordSemFindCode dest (.loc l1 l2 :: xv) cst.code cst.stackSize =
      some (args1, prog, ss) := hfcC
  have hbad' : ¬ wordSemBadDestArgs dest (args.map f) = true := by rw [hbadC]; exact hbad
  have hbadC' : wordSemBadDestArgs dest (args.map f) = false := by rw [hbadC]; exact hbadF
  have hstk : cst.stack = st.stack := by unfold wordStateEqRel at hs; exact hs.2.2.2.1
  have hls : cst.localsSize = st.localsSize := by unfold wordStateEqRel at hs; exact hs.2.2.1
  have hhd : cst.handler = st.handler := by
    unfold wordStateEqRel at hs; exact hs.2.2.2.2.2.2.2.2.2.2.2.1
  have headPrice := invariant f (.call (some (n, (n1, n2), rh, l1, l2)) dest args handler)
  rw [applyColour_call_some] at headPrice
  by_cases hz : st.clock = 0
  · -- TimeOut before the call
    have hEvC : evaluate (applyColour f (.call (some (n, (n1, n2), rh, l1, l2)) dest args handler))
        cst =
        (some .timeOut, flushState true { cst with
          stackMax := (callEnv args1 ss (pushEnv (y1, y2) (colourHandler f handler) cst)).stackMax,
          stack := [] }) := by
      rw [applyColour_call_some]
      exact evaluate_call_ret_timeout cst (n.map f) (applyNummapsKey f (n1, n2)) (applyColour f rh)
        l1 l2 dest (args.map f) (colourHandler f handler) xv args1 prog ss (y1, y2) hgvC hbad' hfcC
        hgC hceC
        (by rw [hclk]; exact hz)
    have hEvS := evaluate_call_ret_timeout {st with permute := st.permute} n (n1, n2) rh l1 l2
      dest args handler xv args1 prog ss (x1, x2) (by rw [getVars_withPermute]; exact hgv) hbad
      hfc hg hce hz
    refine ⟨st.permute, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
    · rw [hEvS, hEvC]
    · rw [hEvS, hEvC]
      apply wsrFlush
      have hS := callEnv_pushEnv_fields args1 ss (x1, x2) handler {st with permute := st.permute}
      have hC := callEnv_pushEnv_fields args1 ss (y1, y2) (colourHandler f handler) cst
      simp only at hS hC
      have hm : (callEnv args1 ss (pushEnv (y1, y2) (colourHandler f handler) cst)).stackMax =
          (callEnv args1 ss (pushEnv (x1, x2) handler {st with permute := st.permute})).stackMax := by
        rw [hC.2.2.2.2.1, hS.2.2.2.2.1, stackSize_pushEnv, stackSize_pushEnv]
        have hsm : cst.stackMax = st.stackMax := by
          unfold wordStateEqRel at hs; exact hs.2.2.2.2.2.1
        rcases handler with _ | ⟨_, _, _, _⟩ <;>
          simp only [colourHandler, hsm, hls, hstk]
      have hs' := hs
      unfold wordStateEqRel at hs' ⊢
      obtain ⟨e1, e2, e3, -, e5, -, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19, e20,
        e21⟩ := hs'
      exact ⟨e1, e2, e3, rfl, e5, hm, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16, e17, e18, e19,
        e20, e21⟩
    · rw [hEvS, hEvC]; rfl
    · rw [applyColour_call_some,
        ret_call_cost_timeout _ (n.map f) (applyNummapsKey f (n1, n2)) (applyColour f rh) l1 l2 dest
          (args.map f) (colourHandler f handler) cst xv hgvC hbadC' args1 prog ss hfcC' hgC (y1, y2)
          hceC (hclk.trans hz),
        ret_call_cost_timeout _ n (n1, n2) rh l1 l2 dest args handler {st with permute := st.permute} xv
          (by rw [getVars_withPermute]; exact hgv) hbadF args1 prog ss hfc' hg (x1, x2) hce hz]
      exact headPrice
  -- the callee runs on pushed frames
  have hhs : handler.isSome = (colourHandler f handler).isSome := by
    rcases handler with _ | ⟨_, _, _, _⟩ <;> rfl
  have hdy2' : sptDomain y2 = fun key => ∃ source, sptDomain x2 source ∧ f source = key := by
    rw [hdx2]; exact hdy2
  have hdy1' : sptDomain y1 = fun key => ∃ source, sptDomain x1 source ∧ f source = key := by
    rw [hdx1]; exact hdy1
  have hr2' : strongLocalsRel f (sptDomain x2) x2 y2 := by rw [hdx2]; exact hr2
  have hr1' : strongLocalsRel f (sptDomain x1) x1 y1 := by rw [hdx1]; exact hr1
  obtain ⟨perm, henv, hsv⟩ := pushEnvSValEq (decClock st) (decClock cst) x2 x1 y2 y1 f handler
    (colourHandler f handler) (wordSemEnvToList y2 cst.permute).2
    ⟨hhd.symm, hstk.symm, hls.symm, hdy2', hi2, hdy1', hi1, hr2',
      by rcases handler with _ | ⟨_, _, _, _⟩ <;> simp [colourHandler]⟩
  rcases hy : wordSemEnvToList y2 cst.permute with ⟨lsC, pmC⟩
  rcases hx : wordSemEnvToList x2 perm with ⟨lsB, pmB⟩
  have henv' := henv
  simp only [decClock] at henv'
  rw [hy, hx] at henv'
  obtain ⟨hpm, hmapB, hinjB⟩ := henv'
  have hperm : (wordSemEnvToList x2 perm).2 = (wordSemEnvToList y2 cst.permute).2 := by
    rw [hx, hy]; exact hpm
  have hSwap := calleeSwap hs x1 x2 y1 y2 handler (colourHandler f handler) hhs perm hperm hsv
    args1 ss
  generalize hS0 : callEnv args1 ss
    (pushEnv (x1, x2) handler {decClock st with permute := perm}) = S0 at hSwap
  generalize hCc : callEnv args1 ss
    (pushEnv (y1, y2) (colourHandler f handler) (decClock cst)) = Cc at hSwap
  have hvS : sValEq S0.stack Cc.stack := by rw [← hS0, ← hCc]; exact hsv
  have hEvC : evaluate (applyColour f (.call (some (n, (n1, n2), rh, l1, l2)) dest args handler))
      cst = callRetTail (n.map f) (applyColour f rh) l1 l2 (y1, y2) (colourHandler f handler)
        (evaluate prog Cc) := by
    rw [applyColour_call_some, ← hCc]
    exact evaluate_call_ret_eq cst (n.map f) (applyNummapsKey f (n1, n2)) (applyColour f rh)
      l1 l2 dest (args.map f) (colourHandler f handler) xv args1 prog ss (y1, y2) hgvC hbad'
      hfcC hgC hceC (by rw [hclk]; exact hz)
  have hEvS : ∀ perm'', evaluate (.call (some (n, (n1, n2), rh, l1, l2)) dest args handler)
      {st with permute := ppPerm perm perm''} =
        callRetTail n rh l1 l2 (x1, x2) handler (evaluate prog {S0 with permute := perm''}) := by
    intro perm''
    rw [evaluate_call_ret_eq {st with permute := ppPerm perm perm''} n (n1, n2) rh l1 l2 dest
      args handler xv args1 prog ss (x1, x2) (by rw [getVars_withPermute]; exact hgv) hbad hfc hg
      hce hz, ← hS0]
    show callRetTail n rh l1 l2 (x1, x2) handler (evaluate prog
      (callEnv args1 ss (pushEnv (x1, x2) handler {decClock st with permute := ppPerm perm perm''}))) = _
    rw [pushEnv_ppPerm]
    rfl
  -- executed work of both calls
  have targetWork : wordExecutionCost (fun p _ => price p)
      (applyColour f (.call (some (n, (n1, n2), rh, l1, l2)) dest args handler)) cst =
      price (.call (some (n.map f, applyNummapsKey f (n1, n2), applyColour f rh, l1, l2)) dest
          (args.map f) (colourHandler f handler)) +
        wordExecutionCost (fun p _ => price p) prog Cc +
        retCont (fun p _ => price p) (n.map f) (applyColour f rh) l1 l2 (colourHandler f handler)
          (y1, y2) (evaluate prog Cc).1 (evaluate prog Cc).2 := by
    rw [applyColour_call_some, ← hCc]
    exact ret_call_cost _ (n.map f) (applyNummapsKey f (n1, n2)) (applyColour f rh) l1 l2 dest
      (args.map f) (colourHandler f handler) cst xv hgvC hbadC' args1 prog ss hfcC' hgC (y1, y2) hceC
      (by rw [hclk]; exact hz) _ _ rfl
  have sourceWork : ∀ perm'', wordExecutionCost (fun p _ => price p)
      (.call (some (n, (n1, n2), rh, l1, l2)) dest args handler) {st with permute := ppPerm perm perm''} =
      price (.call (some (n, (n1, n2), rh, l1, l2)) dest args handler) +
        wordExecutionCost (fun p _ => price p) prog {S0 with permute := perm''} +
        retCont (fun p _ => price p) n rh l1 l2 handler (x1, x2)
          (evaluate prog {S0 with permute := perm''}).1 (evaluate prog {S0 with permute := perm''}).2 := by
    intro perm''
    have suffix := ssa_call_suffix_cost price n (n1, n2) rh l1 l2 dest args handler st perm perm''
      xv args1 prog ss (x1, x2) hgv hbadF hfc' hg hce hz
    rw [hS0] at suffix
    exact suffix
  -- a rejected callee rejects the source call
  by_cases calleeError : (evaluate prog S0).1 = some .error
  · refine ⟨ppPerm perm S0.permute, Or.inl ?_⟩
    rw [hEvS]
    have same : ({S0 with permute := S0.permute} : WordSemStateFiniteExact 64 C F) = S0 := rfl
    rw [same]
    rcases hE : evaluate prog S0 with ⟨r, s⟩
    rw [hE] at calleeError
    dsimp only at calleeError
    subst calleeError
    rfl
  have calleeWork : wordExecutionCost (fun p _ => price p) prog Cc =
      wordExecutionCost (fun p _ => price p) prog S0 := by
    rw [← hSwap]
    exact word_stack_value_executed_cost price prog S0 calleeError Cc.stack hvS
  let Q : Option (WordSemResult 64) × WordSemStateFiniteExact 64 C F → Prop := fun r =>
    (callRetTail n rh l1 l2 (x1, x2) handler r).1 ≠ some .error →
      (callRetTail n rh l1 l2 (x1, x2) handler r).1 =
          (callRetTail (n.map f) (applyColour f rh) l1 l2 (y1, y2) (colourHandler f handler)
            (evaluate prog Cc)).1 ∧
        wordStateEqRel (callRetTail n rh l1 l2 (x1, x2) handler r).2
          (callRetTail (n.map f) (applyColour f rh) l1 l2 (y1, y2) (colourHandler f handler)
            (evaluate prog Cc)).2 ∧
        applyColourLocals f live lt (callRetTail n rh l1 l2 (x1, x2) handler r).1
          (callRetTail n rh l1 l2 (x1, x2) handler r).2.locals
          (callRetTail (n.map f) (applyColour f rh) l1 l2 (y1, y2) (colourHandler f handler)
            (evaluate prog Cc)).2.locals ∧
        retCont (fun p _ => price p) (n.map f) (applyColour f rh) l1 l2 (colourHandler f handler)
            (y1, y2) (evaluate prog Cc).1 (evaluate prog Cc).2 ≤
          retCont (fun p _ => price p) n rh l1 l2 handler (x1, x2) r.1 r.2
  have hmain : ∃ pq, Q ((evaluate prog S0).1, {(evaluate prog S0).2 with permute := pq}) := by
    have hSS := (stackSwapPost_iff _ _).mp (evaluateStackSwap prog S0)
    rcases hE : evaluate prog S0 with ⟨r1, st1⟩
    rw [hE] at hSS
    dsimp only
    have hCrun : ∀ q, evaluate prog {S0 with stack := Cc.stack} = q → evaluate prog Cc = q :=
      fun q h => by rw [← hSwap]; exact h
    rcases r1 with _ | r1
    · exact ⟨st1.permute, fun hne => absurd rfl hne⟩
    cases r1 with
    | error => exact ⟨st1.permute, fun hne => absurd rfl hne⟩
    | «break» _ => exact ⟨st1.permute, fun hne => absurd rfl hne⟩
    | «continue» _ => exact ⟨st1.permute, fun hne => absurd rfl hne⟩
    | timeOut =>
        obtain ⟨-, -, hx⟩ := hSS
        have hc := hCrun _ (hx _ hvS)
        refine ⟨st1.permute, fun _ => ?_⟩
        rw [hc, callRetTail_flush _ _ _ _ _ _ _ _ (Or.inl rfl),
          callRetTail_flush _ _ _ _ _ _ _ _ (Or.inl rfl)]
        dsimp only
        refine ⟨rfl, wsrRefl _, applyColourLocals_flush _ _ _ _ _ (Or.inl rfl), ?_⟩
        rw [retCont_flush _ _ _ _ _ _ _ _ _ (Or.inl rfl)]
        exact Nat.zero_le _
    | notEnoughSpace =>
        obtain ⟨-, -, hx⟩ := hSS
        have hc := hCrun _ (hx _ hvS)
        refine ⟨st1.permute, fun _ => ?_⟩
        rw [hc, callRetTail_flush _ _ _ _ _ _ _ _ (Or.inr (Or.inl rfl)),
          callRetTail_flush _ _ _ _ _ _ _ _ (Or.inr (Or.inl rfl))]
        dsimp only
        refine ⟨rfl, wsrRefl _, applyColourLocals_flush _ _ _ _ _ (Or.inr (Or.inl rfl)), ?_⟩
        rw [retCont_flush _ _ _ _ _ _ _ _ _ (Or.inr (Or.inl rfl))]
        exact Nat.zero_le _
    | finalFfi _ =>
        obtain ⟨-, -, hx⟩ := hSS
        have hc := hCrun _ (hx _ hvS)
        refine ⟨st1.permute, fun _ => ?_⟩
        rw [hc, callRetTail_flush _ _ _ _ _ _ _ _ (Or.inr (Or.inr ⟨_, rfl⟩)),
          callRetTail_flush _ _ _ _ _ _ _ _ (Or.inr (Or.inr ⟨_, rfl⟩))]
        dsimp only
        refine ⟨rfl, wsrRefl _, applyColourLocals_flush _ _ _ _ _ (Or.inr (Or.inr ⟨_, rfl⟩)), ?_⟩
        rw [retCont_flush _ _ _ _ _ _ _ _ _ (Or.inr (Or.inr ⟨_, rfl⟩))]
        exact Nat.zero_le _
    | result x ys =>
        obtain ⟨hk1, hh1, hxS⟩ := hSS
        obtain ⟨st0, hst0, hvst, hkst⟩ := hxS Cc.stack hvS
        have hc := hCrun _ hst0
        by_cases hg2 : x ≠ .loc l1 l2 ∨ ys.length ≠ n.length
        · exact ⟨st1.permute, fun hne => absurd (congrArg Prod.fst
            (callRetTail_result_err n rh l1 l2 (x1, x2) handler x ys _ hg2)) hne⟩
        have hg2' : ¬ (x ≠ .loc l1 l2 ∨ ys.length ≠ (n.map f).length) := by simpa using hg2
        have hkS : sKeyEq (pushEnv (x1, x2) handler {decClock st with permute := perm}).stack
            st1.stack := by rw [← hS0] at hk1; exact hk1
        have hkC : sKeyEq (pushEnv (y1, y2) (colourHandler f handler) (decClock cst)).stack
            st0 := by rw [← hCc] at hkst; exact hkst
        obtain ⟨nS, lS, lsS, optS, hst1st, s1, hpop, hloc1, hdom1, hk1s⟩ :=
          pushEnvPopEnvSKeyEq (x1, x2) handler {decClock st with permute := perm} st1 hkS
        cases hpopP : popEnv {st1 with permute := st1.permute} with
        | none => rw [Flapjack.WordAlloc.popEnv_withPermute, hpop] at hpopP; cases hpopP
        | some _ => ?_
        obtain ⟨nC, lC, lsC', optC, hst0st, cy, hpopC, hlocC, hdomC, hkCy⟩ :=
          pushEnvPopEnvSKeyEq (y1, y2) (colourHandler f handler) (decClock cst)
            {st1 with stack := st0} hkC
        have hW : wordStateEqRel s1 cy := popEnvFrame st1 s1 cy st0
          ⟨hvst, sKeyEqTrans _ _ _ ⟨(sKeyEqSym _ _).mp hk1s,
            by show sKeyEq st.stack cy.stack; rw [← hstk]; exact hkCy⟩,
            hpopC, hpop⟩
        by_cases hd : sptDomainEqUnion s1.locals x1 x2
        case neg =>
          refine ⟨st1.permute, fun hne => absurd ?_ hne⟩
          rw [callRetTail_result_pop n rh l1 l2 (x1, x2) handler x ys
            _ {s1 with permute := st1.permute} hg2
            (by rw [Flapjack.WordAlloc.popEnv_withPermute, hpop]; rfl), if_neg hd]
        have hdC : sptDomainEqUnion cy.locals y1 y2 := by
          intro k
          have := congrFun hdomC k
          show sptDomain cy.locals k ↔ sptDomain y1 k ∨ sptDomain y2 k
          rw [← this]
          exact Or.comm
        have hkeysS := sKeyEqPushEnvImpMapFst {decClock st with permute := perm} x1 x2 handler
          nS (sptToAList x1) lS optS lsS lsB pmB ⟨by rw [← hst1st]; exact hkS, hx⟩
        have hkeysC := sKeyEqPushEnvImpMapFst (decClock cst) y1 y2 (colourHandler f handler)
          nC (sptToAList y1) lC optC lsC' lsC pmC ⟨by rw [← hst0st]; exact hkC, hy⟩
        have hvals : lS.map Prod.snd = lC.map Prod.snd := by
          have hst0st' : st0 = _ := hst0st
          rw [hst1st, hst0st'] at hvst
          exact ((sFrameValEqDef2 _ _ _ _ _ _ _ _).mp hvst.2).1
        have hmapK := keyMapImplies f lsB lsC hmapB
        have hl : lC.map Prod.fst = (lS.map Prod.fst).map f := by
          rw [← hkeysC.1, ← hmapK, hkeysS.1]
        have hkeysB := envToListKeys x2 perm
        rw [hx] at hkeysB
        have hdomL : ∀ a, a ∈ lS.map Prod.fst → sptDomain n2 a := by
          intro a ha
          rw [← hkeysS.1] at ha
          have : sptDomain x2 a := by rw [← hkeysB]; exact ha
          rw [hdx2] at this; exact this
        have hrelAll : ∀ d, strongLocalsRel f d s1.locals cy.locals := by
          intro d
          rw [hloc1, hlocC]
          have hz' : lS = (lS.map Prod.fst).zip (lC.map Prod.snd) := by
            rw [← hvals, zip_map_fst_snd]
          rw [hz']
          refine allocLocalsRel f x1 y1 (lS.map Prod.fst) lC hl ?_ hr1' d
          intro a b ha hb hab
          refine inj12 a b ?_ ?_ hab
          · rcases ha with ha | ha
            · exact Or.inr (hdomL a ha)
            · rw [hdx1] at ha; exact Or.inl ha
          · rcases hb with hb | hb
            · exact Or.inr (hdomL b hb)
            · rw [hdx1] at hb; exact Or.inl hb
        have hX : ∀ k, sptMem k s1.locals →
            sptDomain (numsetListInsert n (sptUnion n2 n1)) k := by
          intro k hk
          have := (congrFun hdom1 k).mpr hk
          rw [sptDomain_numsetIns, sptDomain_uni, hdx2, hdx1] at *
          exact Or.inl this
        have hlenN : n.length = ys.length := by
          have : ¬ ys.length ≠ n.length := fun h => hg2 (Or.inr h)
          exact (Classical.not_not.mp this).symm
        obtain ⟨pq, hpq⟩ := ihRet (setVars n ys s1) (setVars (n.map f) ys cy) f live lt
          ⟨hokRh, wsrLocals _ _ hW,
            strongLocalsRelSetVarsDom n ys f _ _ s1 cy ⟨hlenN, hinjN, hX,
              fun k hk => (sptDomain_numsetIns _ _ _).mpr (Or.inr hk), hrelAll _⟩⟩
        refine ⟨pq, fun hne => ?_⟩
        have hsrc : callRetTail n rh l1 l2 (x1, x2) handler
            (some (.result x ys), {st1 with permute := pq}) =
            evaluate rh {setVars n ys s1 with permute := pq} := by
          rw [callRetTail_result_pop _ _ _ _ _ _ _ _ _ {s1 with permute := pq} hg2
            (by rw [Flapjack.WordAlloc.popEnv_withPermute, hpop]; rfl)]
          exact if_pos hd
        have hcol : callRetTail (n.map f) (applyColour f rh) l1 l2 (y1, y2)
            (colourHandler f handler) (evaluate prog Cc) =
            evaluate (applyColour f rh) (setVars (n.map f) ys cy) := by
          rw [hc, callRetTail_result_pop _ _ _ _ _ _ _ _ _ cy hg2' hpopC]
          exact if_pos hdC
        have srcWork : retCont (fun p _ => price p) n rh l1 l2 handler (x1, x2)
            (some (.result x ys)) {st1 with permute := pq} =
            wordExecutionCost (fun p _ => price p) rh {setVars n ys s1 with permute := pq} :=
          retCont_result_pop _ n rh l1 l2 handler (x1, x2) x ys _ {s1 with permute := pq} hg2
            (by rw [Flapjack.WordAlloc.popEnv_withPermute, hpop]; rfl) hd
        have tgtWork : retCont (fun p _ => price p) (n.map f) (applyColour f rh) l1 l2
            (colourHandler f handler) (y1, y2) (evaluate prog Cc).1 (evaluate prog Cc).2 =
            wordExecutionCost (fun p _ => price p) (applyColour f rh) (setVars (n.map f) ys cy) := by
          rw [hc]
          exact retCont_result_pop _ (n.map f) (applyColour f rh) l1 l2 (colourHandler f handler)
            (y1, y2) x ys _ cy hg2' hpopC hdC
        dsimp only at hne ⊢
        rw [hsrc] at hne ⊢
        rw [hcol, srcWork, tgtWork]
        dsimp only at hpq
        rcases hpq with bad | ⟨same, frame, locals, cost⟩
        · exact absurd bad hne
        · exact ⟨same, frame, locals, cost⟩
    | exception x y =>
        obtain ⟨hlt, e0, e, nn, ls, m, lss, hl, hm, ⟨hfe, hloc⟩, hks, hhn, hxS⟩ := hSS
        have hkeysB := envToListKeys x2 perm
        rw [hx] at hkeysB
        have hkeysC := envToListKeys y2 cst.permute
        rw [hy] at hkeysC
        have hmapK := keyMapImplies f lsB lsC hmapB
        rcases handler with _ | ⟨v, hp, l1', l2'⟩
        · -- no handler: the exception passes through
          have hS0h : S0.handler = st.handler := by rw [← hS0]; rfl
          have hS0st : S0.stack =
              .stackFrame st.localsSize (sptToAList x1) lsB none :: st.stack := by
            rw [← hS0]; show (pushEnv (x1, x2) none {decClock st with permute := perm}).stack = _
            simp only [pushEnv, decClock, hx]
          have hCcst : Cc.stack =
              .stackFrame cst.localsSize (sptToAList y1) lsC none :: cst.stack := by
            rw [← hCc]; show (pushEnv (y1, y2) none (decClock cst)).stack = _
            simp only [pushEnv, decClock, hy]
          have hl0 := hl
          rw [hS0h, hS0st] at hlt hl
          have hle : st.handler + 1 ≤ st.stack.length := by
            rcases Nat.lt_or_ge st.handler st.stack.length with h | h
            · exact h
            · exfalso
              have hlt' : st.handler < st.stack.length + 1 := by simpa using hlt
              have heq : st.handler + 1 = (WordSemStackFrame.stackFrame st.localsSize
                  (sptToAList x1) lsB none :: st.stack).length := by simp; omega
              rw [lastNLengthCond _ _ heq] at hl
              simp at hl
          rw [lastN_cons _ _ _ hle] at hl
          have hlC0 : wordSemLastN (S0.handler + 1) Cc.stack =
              .stackFrame m e0 e (some nn) :: ls := by
            rw [hS0h, hCcst, lastN_cons _ _ _ (by rw [hstk]; exact hle), hstk]; exact hl
          obtain ⟨stt, locs, hstt, ⟨lss', hf', hlocs, hsnd'⟩, hvstt, hkstt⟩ :=
            hxS Cc.stack e0 e ls ⟨hlC0, hvS⟩
          have hc := hCrun _ hstt
          have hlss : lss = lss' := listEq_of_map_fst_snd _ _ (hfe.symm.trans hf') hsnd'
          subst hlss
          have hlocsEq : locs = st1.locals := hlocs.trans hloc.symm
          have hsttEq : stt = st1.stack :=
            (sValAndKeyEq _ _ ⟨hvstt, sKeyEqTrans _ _ _ ⟨hks, hkstt⟩⟩).symm
          refine ⟨st1.permute, fun _ => ?_⟩
          rw [hc, show colourHandler f (none : Option (Nat × WordLangProgHOL (BitVec 64) × Nat ×
            Nat)) = none from rfl, callRetTail_exc_none, callRetTail_exc_none, hlocsEq, hsttEq,
            ← hhn]
          refine ⟨rfl, wsrRefl _, rfl, ?_⟩
          rw [retCont_exc_none]
          exact Nat.zero_le _
        · -- handler: continue with the handler program
          obtain ⟨hinjH, hokHp⟩ := hokH
          have hS0h : S0.handler = st.stack.length := by rw [← hS0]; rfl
          have hS0st : S0.stack = .stackFrame st.localsSize (sptToAList x1) lsB
              (some (st.handler, l1', l2')) :: st.stack := by
            rw [← hS0]; show (pushEnv (x1, x2) (some (v, hp, l1', l2'))
              {decClock st with permute := perm}).stack = _
            simp only [pushEnv, decClock, hx]
          have hCcst : Cc.stack = .stackFrame cst.localsSize (sptToAList y1) lsC
              (some (cst.handler, l1', l2')) :: cst.stack := by
            rw [← hCc]; show (pushEnv (y1, y2) (some (f v, applyColour f hp, l1', l2'))
              (decClock cst)).stack = _
            simp only [pushEnv, decClock, hy]
          rw [hS0h, hS0st, lastNLengthCond _ _ (by simp)] at hl
          simp only [List.cons.injEq, WordSemStackFrame.stackFrame.injEq, Option.some.injEq] at hl
          obtain ⟨⟨hm0, he0, hee, hnn⟩, hls0⟩ := hl
          subst hm0 he0 hee hnn hls0
          have hlC0 : wordSemLastN (S0.handler + 1) Cc.stack =
              .stackFrame st.localsSize (sptToAList y1) lsC (some (st.handler, l1', l2')) ::
                cst.stack := by
            rw [hS0h, hCcst, lastNLengthCond _ _ (by simp [hstk]), hls, hhd]
          obtain ⟨stt, locs, hstt, ⟨lss', hf', hlocs, hsnd'⟩, hvstt, hkstt⟩ :=
            hxS Cc.stack (sptToAList y1) lsC cst.stack ⟨hlC0, hvS⟩
          have hc := hCrun _ hstt
          have hsttEq : stt = st1.stack :=
            (sValAndKeyEq _ _ ⟨hvstt, sKeyEqTrans _ _ _ ⟨hks, by rw [← hstk]; exact hkstt⟩⟩).symm
          by_cases hxg : x ≠ .loc l1' l2'
          · refine ⟨st1.permute, fun hne => absurd ?_ hne⟩
            rw [callRetTail_exc_some, if_pos hxg]
          by_cases hd : sptDomainEqUnion st1.locals x1 x2
          case neg =>
            refine ⟨st1.permute, fun hne => absurd ?_ hne⟩
            rw [callRetTail_exc_some, if_neg hxg, if_neg hd]
          have hkl : lss'.map Prod.fst = (lss.map Prod.fst).map f := by
            rw [← hf', ← hmapK, hfe]
          have hdomL : ∀ a, a ∈ lss.map Prod.fst → sptDomain n2 a := by
            intro a ha
            rw [← hfe] at ha
            have : sptDomain x2 a := by rw [← hkeysB]; exact ha
            rw [hdx2] at this; exact this
          have hrelAll : ∀ d, strongLocalsRel f d st1.locals locs := by
            intro d
            rw [hloc, hlocs]
            have hz' : lss = (lss.map Prod.fst).zip (lss'.map Prod.snd) := by
              rw [← hsnd', zip_map_fst_snd]
            rw [hz']
            refine allocLocalsRel f x1 y1 (lss.map Prod.fst) lss' hkl ?_ hr1' d
            intro a b ha hb hab
            refine inj12 a b ?_ ?_ hab
            · rcases ha with ha | ha
              · exact Or.inr (hdomL a ha)
              · rw [hdx1] at ha; exact Or.inl ha
            · rcases hb with hb | hb
              · exact Or.inr (hdomL b hb)
              · rw [hdx1] at hb; exact Or.inl hb
          have hX : ∀ k, sptMem k st1.locals → sptDomain (sptInsert v () (sptUnion n2 n1)) k := by
            intro k hk
            have hk' : sptDomain st1.locals k := hk
            rw [hloc, sptDomain_frameLocals] at hk'
            rw [sptDomain_ins, sptDomain_uni]
            rcases hk' with hk' | hk'
            · exact Or.inr (Or.inl (hdomL k hk'))
            · rw [hdx1] at hk'; exact Or.inr (Or.inr hk')
          have hdC : sptDomainEqUnion locs y1 y2 := by
            intro k
            show sptDomain locs k ↔ sptDomain y1 k ∨ sptDomain y2 k
            rw [hlocs, sptDomain_frameLocals, ← hf']
            have : k ∈ lsC.map Prod.fst ↔ sptDomain y2 k := by rw [← hkeysC]
            rw [this]
            exact Or.comm
          have hW : wordStateEqRel st1
              {st1 with stack := stt, handler := st.handler, locals := locs} := by
            have hh1 : st.handler = st1.handler := hhn.symm
            rw [hsttEq, hh1]
            exact wsrLocals st1.locals locs (wsrRefl st1)
          obtain ⟨pq, hpq⟩ := ihHandler v hp l1' l2' rfl (setVar v y st1)
            (setVar (f v) y {st1 with stack := stt, handler := st.handler, locals := locs})
            f live lt ⟨hokHp, wsrLocals _ _ hW,
              strongLocalsRelSetVarDom f _ _ v y st1 _ ⟨hinjH, hX,
                (sptDomain_ins _ _ _ _).mpr (Or.inl rfl), hrelAll _⟩⟩
          refine ⟨pq, fun hne => ?_⟩
          have hsrc : callRetTail n rh l1 l2 (x1, x2) (some (v, hp, l1', l2'))
              (some (.exception x y), {st1 with permute := pq}) =
              evaluate hp {setVar v y st1 with permute := pq} := by
            rw [callRetTail_exc_some, if_neg hxg]
            exact if_pos hd
          have hcol : callRetTail (n.map f) (applyColour f rh) l1 l2 (y1, y2)
              (colourHandler f (some (v, hp, l1', l2'))) (evaluate prog Cc) =
              evaluate (applyColour f hp) (setVar (f v) y
                {st1 with stack := stt, handler := st.handler, locals := locs}) := by
            rw [hc]
            show callRetTail (n.map f) (applyColour f rh) l1 l2 (y1, y2)
              (some (f v, applyColour f hp, l1', l2')) _ = _
            rw [callRetTail_exc_some, if_neg hxg]
            exact if_pos hdC
          have srcWork : retCont (fun p _ => price p) n rh l1 l2 (some (v, hp, l1', l2')) (x1, x2)
              (some (.exception x y)) {st1 with permute := pq} =
              wordExecutionCost (fun p _ => price p) hp {setVar v y st1 with permute := pq} :=
            retCont_exc_some _ n rh l1 l2 (x1, x2) x y _ v hp l1' l2' hxg hd
          have tgtWork : retCont (fun p _ => price p) (n.map f) (applyColour f rh) l1 l2
              (colourHandler f (some (v, hp, l1', l2'))) (y1, y2) (evaluate prog Cc).1
              (evaluate prog Cc).2 =
              wordExecutionCost (fun p _ => price p) (applyColour f hp)
                (setVar (f v) y {st1 with stack := stt, handler := st.handler, locals := locs}) := by
            rw [hc]
            exact retCont_exc_some _ (n.map f) (applyColour f rh) l1 l2 (y1, y2) x y _ (f v)
              (applyColour f hp) l1' l2' hxg hdC
          dsimp only at hne ⊢
          rw [hsrc] at hne ⊢
          rw [hcol, srcWork, tgtWork]
          dsimp only at hpq
          rcases hpq with bad | ⟨same, frame, locals, cost⟩
          · exact absurd bad hne
          · exact ⟨same, frame, locals, cost⟩
  obtain ⟨perm'', hQ, calleeSame⟩ := ssa_permute_predicate_cost price prog S0 Q
    (fun post _ hne => absurd rfl hne) hmain
  refine ⟨ppPerm perm perm'', ?_⟩
  dsimp only
  rw [hEvS perm'', hEvC]
  by_cases herr : (callRetTail n rh l1 l2 (x1, x2) handler (evaluate prog {S0 with permute := perm''})).1 =
      some .error
  · exact Or.inl herr
  obtain ⟨h1, h2, h3, h4⟩ := hQ herr
  refine Or.inr ⟨h1, h2, h3, ?_⟩
  rw [targetWork, sourceWork perm'', calleeWork, ← calleeSame]
  omega

#print axioms colourCost_returning
end InitECandidate.Runtime.FineCost
