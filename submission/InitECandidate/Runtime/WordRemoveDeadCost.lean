import InitECandidate.Runtime.WordOptimizerPrice
import InitECandidate.Runtime.WordLineCost
import InitECandidate.Runtime.WordIselLoop
import InitECandidate.Runtime.WordCallExecutionCost
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateRemoveDead
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact Flapjack.WordAlloc

/-! Cost transfer for word_alloc's dead-code removal (`removeDeadProg`), a
same-code step at the single price `wordOptimizerLocalPrice`: dead leaves become
`skip` (price 0), move lists only shrink, and every kept node pays the same.
Run and post come from Flapjack's `removeDeadGoalAll`; `removeDead_run_cost`
and `removeDeadProg_run_cost` expose run, post and cost together. In the call
cases the callee starts from the identical entry state (the relation fixes the
argument values and live cut envs, `callEnv` drops caller locals, `pushEnv`
ignores the handler program), so the callee's work is the same run, not an
assumption about results. -/

/-- Cost half of `evaluate_remove_dead`: under its premises, the dead-code-free
program costs at most the original at the optimizer price. -/
def RemoveDeadCost (C F : Type) (prog : WordLangProgHOL (BitVec 64)) : Prop :=
  ∀ (live : NumSet) (nlive : List WordStoreHOL) (lt : List (NumSet × NumSet))
    (prog' : WordLangProgHOL (BitVec 64)) (livein : NumSet) (nlivein : List WordStoreHOL)
    (st : WordSemStateFiniteExact 64 C F) (t : Spt (WordLocW 64))
    (tstore : HolFiniteMapExact WordStoreHOL (WordLocW 64))
    (res : Option (WordSemResult 64)) (rst : WordSemStateFiniteExact 64 C F),
    strongLocalsRel id (sptDomain livein) st.locals t ∧
      liveStoreRel nlivein st.store tstore ∧
      evaluate prog st = (res, rst) ∧
      flatExpConventions prog = true ∧
      removeDead prog live nlive lt = (prog', livein, nlivein) ∧
      res ≠ some .error →
    wordExecutionCost wordOptimizerLocalPrice prog' { st with locals := t, store := tstore } ≤
      wordExecutionCost wordOptimizerLocalPrice prog st

theorem optimizerPrice_state' {C F : Type} (p : WordLangProgHOL (BitVec 64))
    (s t : WordSemStateFiniteExact 64 C F) : wordOptimizerLocalPrice p s = wordOptimizerLocalPrice p t := by
  cases p <;> rfl

/-- A leaf that dead-code removal keeps or turns into `skip`. -/
theorem rd_leaf_cost {C F : Type} (p : WordLangProgHOL (BitVec 64)) (hp : isLeafProg p = true)
    (s t : WordSemStateFiniteExact 64 C F) (p' : WordLangProgHOL (BitVec 64)) (h : p' = p ∨ p' = .skip) :
    wordExecutionCost wordOptimizerLocalPrice p' t ≤ wordExecutionCost wordOptimizerLocalPrice p s := by
  rcases h with rfl | rfl
  · rw [wordCost_leaf _ hp, wordCost_leaf _ hp, optimizerPrice_state' p' t s]
  · rw [wordCost_leaf _ (by rfl), wordCost_leaf _ hp]
    simp [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice, WordToStack.refinedWordStackLeafBudget]

theorem removeDead_leaf_shape (p : WordLangProgHOL (BitVec 64)) (hp : isLeafProg p = true)
    (hm : ∀ pri ls, p ≠ .move pri ls) (live : NumSet) (nlive : List WordStoreHOL) (lt : List (NumSet × NumSet)) :
    (removeDead p live nlive lt).1 = p ∨ (removeDead p live nlive lt).1 = .skip := by
  cases p <;> simp only [isLeafProg, Bool.false_eq_true] at hp
  case move pri ls => exact absurd rfl (hm pri ls)
  case set st e =>
    cases e
    all_goals rw [removeDead]
    all_goals (repeat' split) <;> simp
  all_goals rw [removeDead]
  all_goals (repeat' split) <;> simp

/-- The leaf cases of the cost goal, other than moves. -/
theorem rdCost_leaf {C F : Type} (p : WordLangProgHOL (BitVec 64)) (hp : isLeafProg p = true)
    (hm : ∀ pri ls, p ≠ .move pri ls) : RemoveDeadCost C F p := by
  intro live nlive lt prog' livein nlivein st t tstore res rst ⟨_, _, _, _, hrd, _⟩
  have shape := removeDead_leaf_shape p hp hm live nlive lt
  rw [hrd] at shape
  exact rd_leaf_cost p hp st _ prog' shape

theorem rdCost_move {C F : Type} (pri : Nat) (ls : List (Nat × Nat)) : RemoveDeadCost C F (.move pri ls) := by
  intro live nlive lt prog' livein nlivein st t tstore res rst ⟨_, _, _, _, hrd, _⟩
  simp only [removeDead] at hrd
  split at hrd
  · simp only [Prod.mk.injEq] at hrd; obtain ⟨rfl, -, -⟩ := hrd
    exact rd_leaf_cost (.move pri ls) rfl st _ _ (Or.inr rfl)
  · simp only [Prod.mk.injEq] at hrd; obtain ⟨rfl, -, -⟩ := hrd
    rw [wordCost_leaf _ rfl, wordCost_leaf _ rfl]
    simp only [wordOptimizerLocalPrice]
    have := List.length_filter_le (fun p => sptLookup p.1 live = some ()) ls
    omega

theorem rdCost_seq {C F : Type} (s1 s2 : WordLangProgHOL (BitVec 64))
    (c1 : RemoveDeadCost C F s1) (c2 : RemoveDeadCost C F s2) : RemoveDeadCost C F (.seq s1 s2) := by
  have hseq := (evaluate_def_rebound (width := 64) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
  rintro live nlive lt prog' livein nlivein st t tstore res rst ⟨hl, hs, hev, hflat, hrd, herr⟩
  simp only [flatExpConventions, Bool.and_eq_true] at hflat
  rw [removeDead] at hrd
  rcases h2 : removeDead s2 live nlive lt with ⟨s2', l2, n2⟩
  rw [h2] at hrd
  dsimp only at hrd
  rcases h1 : removeDead s1 l2 n2 lt with ⟨s1', l1, n1⟩
  rw [h1] at hrd
  dsimp only at hrd
  simp only [Prod.mk.injEq] at hrd
  obtain ⟨hp, rfl, rfl⟩ := hrd
  subst hp
  rcases he1 : evaluate s1 st with ⟨r1, st1⟩
  have hev' := hev
  rw [hseq, he1] at hev'
  dsimp only at hev'
  have herr1 : r1 ≠ some .error := by
    rintro rfl; simp only [Prod.mk.injEq] at hev'; exact herr hev'.1.symm
  obtain ⟨t1, ts1, hT1, hp1⟩ := removeDeadGoalAll s1 l2 n2 lt s1' l1 n1 st t tstore r1 st1
    ⟨hl, hs, he1, hflat.1, h1, herr1⟩
  have k1 := c1 l2 n2 lt s1' l1 n1 st t tstore r1 st1 ⟨hl, hs, he1, hflat.1, h1, herr1⟩
  rw [wordExecutionCost_seq _ s1 s2 st, he1]
  have seq0 : ∀ (a b : WordLangProgHOL (BitVec 64)) (x : WordSemStateFiniteExact 64 C F),
      wordOptimizerLocalPrice (.seq a b) x = 0 := by
    intro a b x; simp [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
      WordToStack.refinedWordStackLeafBudget]
  cases r1 with
  | none =>
    obtain ⟨hl1, hs1⟩ := hp1
    have k2 := c2 live nlive lt s2' l2 n2 st1 t1 ts1 res rst ⟨hl1, hs1, hev', hflat.2, h2, herr⟩
    simp only [seq0]
    split
    · rw [evaluate] at hT1
      simp only [Prod.mk.injEq] at hT1
      rw [hT1.2]; omega
    · omega
    · rw [wordExecutionCost_seq, hT1, seq0]; dsimp only; omega
  | some r =>
    simp only [seq0]
    split
    · rw [evaluate] at hT1; simp only [Prod.mk.injEq] at hT1; cases hT1.1
    · omega
    · rw [wordExecutionCost_seq, hT1, seq0]; dsimp only; omega

theorem rdCost_mustTerminate {C F : Type} (p : WordLangProgHOL (BitVec 64)) (c : RemoveDeadCost C F p) :
    RemoveDeadCost C F (.mustTerminate p) := by
  have hmt := (evaluate_def_rebound (width := 64) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
  rintro live nlive lt prog' livein nlivein st t tstore res rst ⟨hl, hs, hev, hflat, hrd, herr⟩
  simp only [flatExpConventions] at hflat
  rw [removeDead] at hrd
  rcases hp : removeDead p live nlive lt with ⟨p', l1, n1⟩
  rw [hp] at hrd
  dsimp only at hrd
  simp only [Prod.mk.injEq] at hrd
  obtain ⟨rfl, rfl, rfl⟩ := hrd
  rw [hmt] at hev
  have mt0 : ∀ (q : WordLangProgHOL (BitVec 64)) (x : WordSemStateFiniteExact 64 C F),
      wordOptimizerLocalPrice (.mustTerminate q) x = 0 := by
    intro q x; simp [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
      WordToStack.refinedWordStackLeafBudget]
  by_cases hz : st.termdep = 0
  · simp only [hz, if_true, Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  · simp only [hz, if_false] at hev
    generalize hL : wordSemMustTerminateLimit 64 = L at hev
    rcases hb : evaluate p { st with clock := L, termdep := st.termdep - 1 } with ⟨r, s1⟩
    rw [hb] at hev
    dsimp only at hev
    have herr' : r ≠ some .error := by
      rintro rfl; simp only [Prod.mk.injEq] at hev; exact herr hev.1.symm
    have k := c live nlive lt p' l1 n1 { st with clock := L, termdep := st.termdep - 1 } t tstore r s1
      ⟨hl, hs, hb, hflat, hp, herr'⟩
    rw [wordExecutionCost, wordExecutionCost, dif_neg hz, mt0, mt0]
    have hz' : ¬ ({ st with locals := t, store := tstore } : WordSemStateFiniteExact 64 C F).termdep = 0 := hz
    rw [dif_neg hz', hL]
    simpa using k

theorem rdCost_ite {C F : Type} (cmp : Cmp) (r1 : Nat) (ri : WordRegImm (BitVec 64)) (e2 e3 : WordLangProgHOL (BitVec 64))
    (c2 : RemoveDeadCost C F e2) (c3 : RemoveDeadCost C F e3) : RemoveDeadCost C F (.ite cmp r1 ri e2 e3) := by
  have hite := (evaluate_def_rebound (width := 64) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rintro live nlive lt prog' livein nlivein st t tstore res rst ⟨hl, hs, hev, hflat, hrd, herr⟩
  simp only [flatExpConventions, Bool.and_eq_true] at hflat
  rw [removeDead] at hrd
  rcases h2 : removeDead e2 live nlive lt with ⟨e2', l2, n2⟩
  rcases h3 : removeDead e3 live nlive lt with ⟨e3', l3, n3⟩
  rw [h2, h3] at hrd
  dsimp only at hrd
  simp only [Prod.mk.injEq] at hrd
  obtain ⟨hp, hlv, rfl⟩ := hrd
  have hsub : ∀ k, sptDomain l2 k ∨ sptDomain l3 k → sptDomain livein k := by
    intro k hk
    rw [← hlv]
    cases ri <;> simp only [sptDomain_ins, sptDomain_sptUnion] <;> simp [hk]
  have hr1 : sptDomain livein r1 := by
    rw [← hlv]
    cases ri <;> simp only [sptDomain_ins] <;> simp
  have hr2 : ∀ r2, ri = .reg r2 → sptDomain livein r2 := by
    rintro r2 rfl
    rw [← hlv]
    simp only [sptDomain_ins]; simp
  have hl2 : strongLocalsRel id (sptDomain l2) st.locals t :=
    fun k v ⟨hk, hv⟩ => hl k v ⟨hsub k (Or.inl hk), hv⟩
  have hl3 : strongLocalsRel id (sptDomain l3) st.locals t :=
    fun k v ⟨hk, hv⟩ => hl k v ⟨hsub k (Or.inr hk), hv⟩
  have hs2 : liveStoreRel n2 st.store tstore :=
    liveStoreRelLess _ _ _ _ ⟨hs, filterSub _ _⟩
  have hs3 : liveStoreRel n3 st.store tstore :=
    liveStoreRelLess _ _ _ _ ⟨hs, fun x hx => by simpa using (List.mem_filter.mp hx).2⟩
  rw [hite] at hev
  -- the kept `ite` costs at most the source; a dropped one costs nothing
  suffices key : wordExecutionCost wordOptimizerLocalPrice (.ite cmp r1 ri e2' e3') { st with locals := t, store := tstore } ≤
      wordExecutionCost wordOptimizerLocalPrice (.ite cmp r1 ri e2 e3) st by
    subst hp
    split
    · rw [wordCost_leaf _ (by rfl)]
      simp [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice, WordToStack.refinedWordStackLeafBudget]
    · exact key
  cases hx : getVar r1 st with
  | none => rw [hx] at hev; simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  | some x =>
    cases hy : WordSemStateFiniteExact.getVarImm ri st with
    | none => rw [hx, hy] at hev; simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
    | some y =>
      rw [hx, hy] at hev
      dsimp only at hev
      have htx : getVar r1 { st with locals := t, store := tstore } = some x :=
        hl r1 x ⟨hr1, hx⟩
      have hty : WordSemStateFiniteExact.getVarImm ri { st with locals := t, store := tstore } =
          some y := by
        cases ri with
        | reg r2 =>
          simp only [WordSemStateFiniteExact.getVarImm] at hy ⊢
          exact hl r2 y ⟨hr2 r2 rfl, hy⟩
        | imm w => simpa [WordSemStateFiniteExact.getVarImm] using hy
      rw [wordExecutionCost, wordExecutionCost, hx, hy, htx, hty]
      dsimp only
      have pr : wordOptimizerLocalPrice (.ite cmp r1 ri e2' e3') { st with locals := t, store := tstore } =
          wordOptimizerLocalPrice (.ite cmp r1 ri e2 e3) st := by
        simp [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice, WordToStack.refinedWordStackLeafBudget]
      rw [pr]
      cases hc : wordSemWordCmp cmp x y with
      | none => simp
      | some b =>
        rw [hc] at hev
        cases b with
        | true =>
          have := c2 live nlive lt e2' l2 n2 st t tstore res rst ⟨hl2, hs2, hev, hflat.1, h2, herr⟩
          dsimp only; omega
        | false =>
          have := c3 live nlive lt e3' l3 n3 st t tstore res rst ⟨hl3, hs3, hev, hflat.2, h3, herr⟩
          dsimp only; omega

/-- Loop iterations by clock induction: each body run starts from the same cut
state on both sides; the next iteration starts from the target body's actual
final state (`removeDeadGoalAll`), related to the source's on the loop names. -/
theorem rdCost_loop_aux {C F : Type} (names : NumSet) (body : WordLangProgHOL (BitVec 64)) (exitNames : NumSet)
    (lt : List (NumSet × NumSet)) (cb : RemoveDeadCost C F body) (hflat : flatExpConventions body = true) :
    ∀ (n : Nat) (st : WordSemStateFiniteExact 64 C F), st.clock = n →
      ∀ (t : Spt (WordLocW 64)) (res : Option (WordSemResult 64)) (rst : WordSemStateFiniteExact 64 C F),
      strongLocalsRel id (sptDomain names) st.locals t →
      evaluate (.loop names body exitNames) st = (res, rst) → res ≠ some .error →
      wordExecutionCost wordOptimizerLocalPrice
          (.loop names (removeDead body names [] ((names, exitNames) :: lt)).1 exitNames) { st with locals := t } ≤
        wordExecutionCost wordOptimizerLocalPrice (.loop names body exitNames) st := by
  have ht := (evaluate_def_rebound (width := 64) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro st hn t res rst hl hev herr
  rcases hrdb : removeDead body names [] ((names, exitNames) :: lt) with ⟨body', liveb, nliveb⟩
  dsimp only
  rw [ht] at hev
  cases hcut : cutState (names, .ln) st with
  | none => rw [hcut] at hev; simp only [Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  | some entry =>
    rw [hcut] at hev
    dsimp only at hev
    have hcutT := cutStateRemoveDead names st entry t st.store hl hcut
    have hentryStore : entry.store = st.store := by
      unfold cutState at hcut
      cases henv : wordSemCutEnv (names, .ln) st.locals with
      | none => rw [henv] at hcut; cases hcut
      | some env => rw [henv] at hcut; cases hcut; rfl
    have hentryT : { entry with store := st.store } = entry := by rw [← hentryStore]
    rw [hentryT] at hcutT
    have hcutT' : cutState (names, .ln) { st with locals := t } = some entry := hcutT
    rcases hb : evaluate body entry with ⟨r1, s1⟩
    rw [hb] at hev
    dsimp only at hev
    have herr' : r1 ≠ some .error := by
      rintro rfl
      simp only [wordSemContLoop, Bool.false_eq_true, if_false, wordSemExitLoop, Prod.mk.injEq] at hev
      exact herr hev.1.symm
    obtain ⟨t1, ts1, hbT, hpost⟩ := removeDeadGoalAll body names [] ((names, exitNames) :: lt) body' liveb nliveb
      entry entry.locals entry.store r1 s1 ⟨strongLocalsRelIdRefl _ _, liveStoreRelRefl _ _, hb, hflat, hrdb, herr'⟩
    have kb := cb names [] ((names, exitNames) :: lt) body' liveb nliveb entry entry.locals entry.store r1 s1
      ⟨strongLocalsRelIdRefl _ _, liveStoreRelRefl _ _, hb, hflat, hrdb, herr'⟩
    have e0 : ({ entry with locals := entry.locals, store := entry.store } : WordSemStateFiniteExact 64 C F) = entry := rfl
    rw [e0] at hbT
    replace kb : wordExecutionCost wordOptimizerLocalPrice body' entry ≤
        wordExecutionCost wordOptimizerLocalPrice body entry := kb
    have costS := loop_cost_clause wordOptimizerLocalPrice names body exitNames st entry hcut r1 s1 hb
    have costT := loop_cost_clause wordOptimizerLocalPrice names body' exitNames { st with locals := t } entry hcutT'
      r1 { s1 with locals := t1, store := ts1 } hbT
    have pr : wordOptimizerLocalPrice (.loop names body' exitNames) { st with locals := t } =
        wordOptimizerLocalPrice (.loop names body exitNames) st := by
      simp [wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice, WordToStack.refinedWordStackLeafBudget]
    rw [costS, costT, pr]
    by_cases hcont : wordSemContLoop r1 = true
    · simp only [hcont, if_true] at hev ⊢
      -- the continuing results: `none` and `continue 0`
      have rel1 : strongLocalsRel id (sptDomain names) s1.locals t1 ∧ s1.store = ts1 := by
        rcases r1 with _ | (_ | _ | (_ | k) | (_ | k) | _ | _ | _ | _)
        all_goals try (simp [wordSemContLoop] at hcont; done)
        · exact ⟨hpost.1, (liveStoreRelNil _ _).mp hpost.2⟩
        · exact ⟨by simpa [sptOel] using hpost.2, hpost.1⟩
      obtain ⟨hl1, rfl⟩ := rel1
      by_cases hz : s1.clock = 0
      · simp only [hz, if_true]
        exact Nat.add_le_add_right (Nat.add_le_add_left kb _) 0
      · simp only [hz, if_false, wordSemSTOP] at hev ⊢
        have hlt : (decClock s1).clock < n := by
          have := loopBodyRecursiveClockLt (names, .ln) body st entry s1 r1 hcut hb hz
          omega
        have k2 := ih _ hlt (decClock s1) rfl t1 res rst hl1 hev herr
        have k3 : wordExecutionCost wordOptimizerLocalPrice (.loop names body' exitNames)
              (decClock ({ s1 with locals := t1, store := s1.store } : WordSemStateFiniteExact 64 C F)) ≤
            wordExecutionCost wordOptimizerLocalPrice (.loop names body exitNames) (decClock s1) := by
          rw [hrdb] at k2; exact k2
        exact Nat.add_le_add (Nat.add_le_add_left kb _) k3
    · simp only [hcont, Bool.false_eq_true, if_false]
      exact Nat.add_le_add_right (Nat.add_le_add_left kb _) 0

theorem rdCost_loop {C F : Type} (names : NumSet) (body : WordLangProgHOL (BitVec 64)) (exitNames : NumSet)
    (cb : RemoveDeadCost C F body) : RemoveDeadCost C F (.loop names body exitNames) := by
  rintro live nlive lt prog' livein nlivein st t tstore res rst ⟨hl, hs, hev, hflat, hrd, herr⟩
  simp only [flatExpConventions] at hflat
  rw [removeDead_loop] at hrd
  simp only [Prod.mk.injEq] at hrd
  obtain ⟨rfl, rfl, rfl⟩ := hrd
  have hst : st.store = tstore := (liveStoreRelNil _ _).mp hs
  subst hst
  exact rdCost_loop_aux names body exitNames lt cb hflat st.clock st rfl t res rst hl hev herr

/-- Non-returning calls are kept as they are; the callee starts from
`callEnv` of the arguments, which `strongLocalsRel` makes identical on both
sides, so the whole call costs the same. -/
theorem rdCost_callNone {C F : Type} (dest : Option Nat) (args : List Nat)
    (h : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat)) : RemoveDeadCost C F (.call none dest args h) := by
  have ht := (evaluate_def_rebound (width := 64) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rintro live nlive lt prog' livein nlivein st t tstore res rst ⟨hl, hs, hev, -, hrd, herr⟩
  rw [removeDead] at hrd
  simp only [getLive, Prod.mk.injEq] at hrd
  obtain ⟨rfl, rfl, rfl⟩ := hrd
  have hst : st.store = tstore := (liveStoreRelNil _ _).mp hs
  subst hst
  rw [ht] at hev
  rcases hg : WordSemStateFiniteExact.getVars args st with _ | xs
  · simp only [hg, Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  have hgT : WordSemStateFiniteExact.getVars args ({ st with locals := t, store := st.store } :
      WordSemStateFiniteExact 64 C F) = some xs :=
    (getVarsLocalsEq { st with locals := t, store := st.store } { st with locals := t } rfl _).trans
      (strongLocalsRelIGetVars' args _ st t xs
        ⟨fun x hx => (sptDomain_numsetIns _ _ _).mpr (Or.inr hx), hl, hg⟩)
  apply le_of_eq
  rw [wordExecutionCost, wordExecutionCost]
  simp only [hg, hgT]
  rfl

/-- Returning calls with the return/handler programs replaced: the callee runs
from the identical entry state (`callEnv` drops the caller locals, the cut
envs agree on the live cut set, `pushEnv` ignores the handler program), so the
callee's work and result are the same run; only the continuation programs
differ, and they start from the same state. -/
theorem rdCost_callSome_core {C F : Type} (n : List Nat) (names : WordLangCutsetsHOL)
    (retH retH' : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    (h h' : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (hh : (h = none ∧ h' = none) ∨ ∃ hn hp hp' a b, h = some (hn, hp, a, b) ∧ h' = some (hn, hp', a, b) ∧
      ∀ (S : WordSemStateFiniteExact 64 C F) res rst, evaluate hp S = (res, rst) → res ≠ some .error →
        wordExecutionCost wordOptimizerLocalPrice hp' S ≤ wordExecutionCost wordOptimizerLocalPrice hp S)
    (cret : ∀ (S : WordSemStateFiniteExact 64 C F) res rst, evaluate retH S = (res, rst) → res ≠ some .error →
        wordExecutionCost wordOptimizerLocalPrice retH' S ≤ wordExecutionCost wordOptimizerLocalPrice retH S)
    (st : WordSemStateFiniteExact 64 C F) (t : Spt (WordLocW 64))
    (hl : strongLocalsRel id (sptDomain (sptUnion (sptUnion names.1 names.2) (numsetListInsert args .ln))) st.locals t)
    (res : Option (WordSemResult 64)) (rst : WordSemStateFiniteExact 64 C F)
    (hev : evaluate (.call (some (n, names, retH, l1, l2)) dest args h) st = (res, rst)) (herr : res ≠ some .error) :
    wordExecutionCost wordOptimizerLocalPrice (.call (some (n, names, retH', l1, l2)) dest args h') { st with locals := t } ≤
      wordExecutionCost wordOptimizerLocalPrice (.call (some (n, names, retH, l1, l2)) dest args h) st := by
  have ht := (evaluate_def_rebound (width := 64) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hpush : ∀ (envs : Spt (WordLocW 64) × Spt (WordLocW 64)) (x : WordSemStateFiniteExact 64 C F),
      pushEnv envs h' x = pushEnv envs h x := by
    rcases hh with ⟨rfl, rfl⟩ | ⟨hn, hp, hp', a, b, rfl, rfl, -⟩ <;> intros <;> rfl
  have hpr : ∀ (x y : WordSemStateFiniteExact 64 C F),
      wordOptimizerLocalPrice (.call (some (n, names, retH', l1, l2)) dest args h') x =
        wordOptimizerLocalPrice (.call (some (n, names, retH, l1, l2)) dest args h) y := by
    rcases hh with ⟨rfl, rfl⟩ | ⟨hn, hp, hp', a, b, rfl, rfl, -⟩ <;> intros <;> rfl
  rw [ht] at hev
  rcases hg : WordSemStateFiniteExact.getVars args st with _ | xs
  · simp only [hg, Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  have hgT : WordSemStateFiniteExact.getVars args ({ st with locals := t } : WordSemStateFiniteExact 64 C F) = some xs :=
    strongLocalsRelIGetVars' args _ st t xs
      ⟨fun x hx => by
        rw [sptDomain_sptUnion]
        exact Or.inr ((sptDomain_numsetIns _ _ _).mpr (Or.inr hx)), hl, hg⟩
  simp only [hg] at hev
  by_cases hbad : wordSemBadDestArgs dest args = true
  · simp only [hbad, if_true, Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  have hbad' : wordSemBadDestArgs dest args = false := by simpa using hbad
  simp only [hbad', Bool.false_eq_true, if_false, wordSemAddRetLoc] at hev
  rcases hf : wordSemFindCode dest (.loc l1 l2 :: xs) st.code st.stackSize with _ | ⟨args1, prog, ss⟩
  · simp only [hf, Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  simp only [hf] at hev
  by_cases hdc : sptDomainEmpty names.1 ∨ ¬ n.Nodup
  · simp only [hdc, if_true, Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  simp only [hdc, if_false] at hev
  rcases hce : wordSemCutEnvs names st.locals with _ | envs
  · simp only [hce, Prod.mk.injEq] at hev; exact absurd hev.1.symm herr
  have hceT : wordSemCutEnvs names t = some envs :=
    strongLocalsRelICutEnvs names st t envs ⟨fun k v ⟨hk, hv⟩ => hl k v ⟨by
      rw [sptDomain_sptUnion, sptDomain_sptUnion]; exact Or.inl hk, hv⟩, hce⟩
  simp only [hce] at hev
  by_cases hz : st.clock = 0
  · have hzT : ({ st with locals := t } : WordSemStateFiniteExact 64 C F).clock = 0 := hz
    rw [wordExecutionCost, wordExecutionCost]
    simp only [hg, hgT, hbad', Bool.false_eq_true, if_false, wordSemAddRetLoc, hf, hdc, hce, hceT]
    simp only [hz, dite_true]
    exact le_of_eq (hpr _ _)
  simp only [hz, if_false] at hev
  rcases hcv : evaluate prog (callEnv args1 ss (pushEnv envs h (decClock st))) with ⟨rc, s2⟩
  rw [hcv] at hev
  -- the callee entry state does not see the caller locals
  have hentry : ∀ hx : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat),
      callEnv args1 ss (pushEnv envs hx (decClock ({ st with locals := t } : WordSemStateFiniteExact 64 C F))) =
        callEnv args1 ss (pushEnv envs hx (decClock st)) := by
    intro hx; rcases hx with _ | ⟨_, _, _, _⟩ <;> rfl
  have hcvT : evaluate prog (callEnv args1 ss (pushEnv envs h' (decClock ({ st with locals := t } :
      WordSemStateFiniteExact 64 C F)))) = (rc, s2) := by
    rw [hpush, hentry]; exact hcv
  have costS := ret_call_cost wordOptimizerLocalPrice n names retH l1 l2 dest args h st xs hg hbad' args1 prog ss hf
    hdc envs hce hz rc s2 hcv
  have costT := ret_call_cost wordOptimizerLocalPrice n names retH' l1 l2 dest args h' { st with locals := t } xs hgT
    hbad' args1 prog ss hf hdc envs hceT hz rc s2 hcvT
  have body : wordExecutionCost wordOptimizerLocalPrice prog (callEnv args1 ss (pushEnv envs h' (decClock
      ({ st with locals := t } : WordSemStateFiniteExact 64 C F)))) =
      wordExecutionCost wordOptimizerLocalPrice prog (callEnv args1 ss (pushEnv envs h (decClock st))) := by
    rw [hpush, hentry]
  rw [costS, costT, body, hpr _ st]
  apply Nat.add_le_add_left
  rcases rc with _ | (⟨x, ys⟩ | ⟨x, y⟩ | k | k | _ | _ | _ | _)
  all_goals try (exact Nat.le_refl 0)
  · -- result: the return continuation
    simp only at hev
    simp only [retCont]
    by_cases hx : x ≠ WordLocW.loc l1 l2 ∨ ys.length ≠ n.length
    · simp only [hx, if_true]; exact Nat.le_refl 0
    simp only [hx, if_false] at hev ⊢
    rcases hp : popEnv s2 with _ | s1
    · exact Nat.le_refl 0
    simp only [hp] at hev
    by_cases hdom : sptDomainEqUnion s1.locals envs.1 envs.2
    · simp only [hdom, if_true] at hev ⊢
      exact cret _ res rst hev herr
    · simp only [hdom]; exact Nat.le_refl 0
  · -- exception: the handler
    rcases hh with ⟨rfl, rfl⟩ | ⟨hn, hp, hp', a, b, rfl, rfl, chd⟩
    · simp only [retCont]; exact Nat.le_refl 0
    simp only at hev
    simp only [retCont]
    by_cases hx : x ≠ WordLocW.loc a b
    · rw [if_pos hx, if_pos hx]
    rw [if_neg hx, if_neg hx]
    rw [if_neg hx] at hev
    by_cases hdom : sptDomainEqUnion s2.locals envs.1 envs.2
    · simp only [hdom, if_true] at hev ⊢
      exact chd _ res rst hev herr
    · simp only [hdom]; exact Nat.le_refl 0

theorem rdCost_callSome {C F : Type} (n : List Nat) (names : WordLangCutsetsHOL) (retH : WordLangProgHOL (BitVec 64))
    (l1 l2 : Nat) (dest : Option Nat) (args : List Nat) (h : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (cRet : RemoveDeadCost C F retH) (cH : ∀ hn hp a b, h = some (hn, hp, a, b) → RemoveDeadCost C F hp) :
    RemoveDeadCost C F (.call (some (n, names, retH, l1, l2)) dest args h) := by
  rintro live nlive lt prog' livein nlivein st t tstore res rst ⟨hl, hs, hev, hflat, hrd, herr⟩
  unfold flatExpConventions at hflat
  simp only [Bool.and_eq_true] at hflat
  obtain ⟨hfRet, hfH⟩ := hflat
  have cret : ∀ (S : WordSemStateFiniteExact 64 C F) res rst, evaluate retH S = (res, rst) → res ≠ some .error →
      wordExecutionCost wordOptimizerLocalPrice (removeDead retH live nlive lt).1 S ≤
        wordExecutionCost wordOptimizerLocalPrice retH S := by
    intro S r q run err
    rcases hrr : removeDead retH live nlive lt with ⟨r', lr, nr⟩
    exact cRet live nlive lt r' lr nr S S.locals S.store r q ⟨strongLocalsRelIdRefl _ _, liveStoreRelRefl _ _, run,
      hfRet, hrr, err⟩
  rcases h with _ | ⟨hn, hp, a, b⟩
  · rw [removeDead] at hrd
    simp only [Prod.mk.injEq] at hrd
    obtain ⟨rfl, rfl, rfl⟩ := hrd
    have hst : st.store = tstore := (liveStoreRelNil _ _).mp hs
    subst hst
    exact rdCost_callSome_core n names retH _ l1 l2 dest args none none (Or.inl ⟨rfl, rfl⟩) cret st t hl res rst
      hev herr
  · rw [removeDead] at hrd
    simp only [Prod.mk.injEq] at hrd
    obtain ⟨rfl, rfl, rfl⟩ := hrd
    have hst : st.store = tstore := (liveStoreRelNil _ _).mp hs
    subst hst
    have chd : ∀ (S : WordSemStateFiniteExact 64 C F) res rst, evaluate hp S = (res, rst) → res ≠ some .error →
        wordExecutionCost wordOptimizerLocalPrice (removeDead hp live nlive lt).1 S ≤
          wordExecutionCost wordOptimizerLocalPrice hp S := by
      intro S r q run err
      rcases hrh : removeDead hp live nlive lt with ⟨r', lr, nr⟩
      exact cH hn hp a b rfl live nlive lt r' lr nr S S.locals S.store r q ⟨strongLocalsRelIdRefl _ _,
        liveStoreRelRefl _ _, run, by simpa using hfH, hrh, err⟩
    exact rdCost_callSome_core n names retH _ l1 l2 dest args _ _
      (Or.inr ⟨hn, hp, _, a, b, rfl, rfl, chd⟩) cret st t hl res rst hev herr

/-- Every program satisfies the cost goal: the case assembly mirroring
Flapjack's `removeDeadGoalAll`. -/
theorem rdCostAll {C F : Type} : ∀ prog : WordLangProgHOL (BitVec 64), RemoveDeadCost C F prog
  | .skip => rdCost_leaf _ rfl (by intros; simp)
  | .move pri ls => rdCost_move pri ls
  | .inst i => rdCost_leaf _ rfl (by intros; simp)
  | .assign a b => rdCost_leaf _ rfl (by intros; simp)
  | .get v name => rdCost_leaf _ rfl (by intros; simp)
  | .set v e => rdCost_leaf _ rfl (by intros; simp)
  | .store a b => rdCost_leaf _ rfl (by intros; simp)
  | .mustTerminate p => rdCost_mustTerminate p (rdCostAll p)
  | .call none dest args h => rdCost_callNone dest args h
  | .call (some (n, names, retH, l1, l2)) dest args none =>
      rdCost_callSome n names retH l1 l2 dest args none (rdCostAll retH) (fun _ _ _ _ h => by cases h)
  | .call (some (n, names, retH, l1, l2)) dest args (some (hn, hp, a, b)) =>
      have ihp := rdCostAll hp
      rdCost_callSome n names retH l1 l2 dest args (some (hn, hp, a, b)) (rdCostAll retH)
        (fun _ _ _ _ h => by cases h; exact ihp)
  | .seq s1 s2 => rdCost_seq s1 s2 (rdCostAll s1) (rdCostAll s2)
  | .ite cmp r ri e2 e3 => rdCost_ite cmp r ri e2 e3 (rdCostAll e2) (rdCostAll e3)
  | .loop names body exitNames => rdCost_loop names body exitNames (rdCostAll body)
  | .alloc n names => rdCost_leaf _ rfl (by intros; simp)
  | .storeConsts a b c d w => rdCost_leaf _ rfl (by intros; simp)
  | .raise n => rdCost_leaf _ rfl (by intros; simp)
  | .return n ms => rdCost_leaf _ rfl (by intros; simp)
  | .break k => rdCost_leaf _ rfl (by intros; simp)
  | .continue k => rdCost_leaf _ rfl (by intros; simp)
  | .tick => rdCost_leaf _ rfl (by intros; simp)
  | .opCurrHeap b d s => rdCost_leaf _ rfl (by intros; simp)
  | .locValue r l => rdCost_leaf _ rfl (by intros; simp)
  | .install p l dp dl names => rdCost_leaf _ rfl (by intros; simp)
  | .codeBufferWrite r1 r2 => rdCost_leaf _ rfl (by intros; simp)
  | .dataBufferWrite r1 r2 => rdCost_leaf _ rfl (by intros; simp)
  | .ffi f p1 l1 p2 l2 names => rdCost_leaf _ rfl (by intros; simp)
  | .shareInst op v e => rdCost_leaf _ rfl (by intros; simp)

/-- Combined endpoint for one `removeDead` step: under `evaluate_remove_dead`'s
premises (the genuine `strongLocalsRel`/`liveStoreRel` relation), the
dead-code-free program's actual run from the related state, its
`removeDeadPost` relation, and its executed cost at most the source's, all at
`wordOptimizerLocalPrice` over the same code table. -/
theorem removeDead_run_cost {C F : Type} (prog : WordLangProgHOL (BitVec 64)) (live : NumSet)
    (nlive : List WordStoreHOL) (lt : List (NumSet × NumSet)) (prog' : WordLangProgHOL (BitVec 64)) (livein : NumSet)
    (nlivein : List WordStoreHOL) (st : WordSemStateFiniteExact 64 C F) (t : Spt (WordLocW 64))
    (tstore : HolFiniteMapExact WordStoreHOL (WordLocW 64)) (res : Option (WordSemResult 64))
    (rst : WordSemStateFiniteExact 64 C F)
    (hrel : strongLocalsRel id (sptDomain livein) st.locals t) (hstore : liveStoreRel nlivein st.store tstore)
    (run : evaluate prog st = (res, rst)) (flat : flatExpConventions prog = true)
    (hrd : removeDead prog live nlive lt = (prog', livein, nlivein)) (ok : res ≠ some .error) :
    ∃ (t' : Spt (WordLocW 64)) (tstore' : HolFiniteMapExact WordStoreHOL (WordLocW 64)),
      evaluate prog' { st with locals := t, store := tstore } = (res, { rst with locals := t', store := tstore' }) ∧
      removeDeadPost live nlive lt res rst t' tstore' ∧
      wordExecutionCost wordOptimizerLocalPrice prog' { st with locals := t, store := tstore } ≤
        wordExecutionCost wordOptimizerLocalPrice prog st := by
  obtain ⟨t', ts', hT, hpost⟩ := removeDeadGoalAll prog live nlive lt prog' livein nlivein st t tstore res rst
    ⟨hrel, hstore, run, flat, hrd, ok⟩
  exact ⟨t', ts', hT, hpost, rdCostAll prog live nlive lt prog' livein nlivein st t tstore res rst
    ⟨hrel, hstore, run, flat, hrd, ok⟩⟩

/-- `evaluate_remove_dead_prog`'s locals relation: equal final locals except
after `none`, `break` and `continue`. -/
def RemoveDeadProgPost (res : Option (WordSemResult 64)) (a b : Spt (WordLocW 64)) : Prop :=
  match res with
  | none => True
  | some (.break _) => True
  | some (.continue _) => True
  | some _ => a = b

/-- Combined endpoint for the pipeline's `removeDeadProg` (same code table):
same result, the final state up to locals (locals equal outside `none`/`break`/
`continue`), and executed cost at most the source's. -/
theorem removeDeadProg_run_cost {C F : Type} (prog : WordLangProgHOL (BitVec 64))
    (st rst : WordSemStateFiniteExact 64 C F) (res : Option (WordSemResult 64))
    (flat : flatExpConventions prog = true) (run : evaluate prog st = (res, rst)) (ok : res ≠ some .error) :
    ∃ t' : Spt (WordLocW 64),
      evaluate (removeDeadProg prog) st = (res, { rst with locals := t' }) ∧
      RemoveDeadProgPost res rst.locals t' ∧
      wordExecutionCost wordOptimizerLocalPrice (removeDeadProg prog) st ≤
        wordExecutionCost wordOptimizerLocalPrice prog st := by
  obtain ⟨t', hT, hpost⟩ := evaluateRemoveDeadProg prog st rst res ⟨flat, run, ok⟩
  refine ⟨t', hT, ?_, ?_⟩
  · rcases res with _ | r
    · trivial
    · cases r <;> exact hpost
  rcases hrd : removeDead prog .ln [] [] with ⟨prog', livein, nlivein⟩
  have k := rdCostAll prog .ln [] [] prog' livein nlivein st st.locals st.store res rst
    ⟨strongLocalsRelIdRefl _ _, liveStoreRelRefl _ _, run, flat, hrd, ok⟩
  simp only [removeDeadProg, hrd]
  exact k

#print axioms removeDead_run_cost
#print axioms removeDeadProg_run_cost
#print axioms rdCostAll
#print axioms rdCost_callSome_core
#print axioms rdCost_callNone
#print axioms rdCost_loop
#print axioms rdCost_ite
#print axioms rdCost_leaf
#print axioms rdCost_move
#print axioms rdCost_seq
#print axioms rdCost_mustTerminate
end InitECandidate.Runtime.FineCost
