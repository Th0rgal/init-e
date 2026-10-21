import InitECandidate.Runtime.LoopWordCostLoopBase
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact

/-! The Loop `loop` rules of the Loop-to-Word cost transfer. -/

theorem compHOL_loop (ctxt : Spt Nat) (liveIn liveOut : NumSet) (body : HolLoopProg 64) (l : Nat × Nat) :
    (LoopToWord.compHOL ctxt (.loop liveIn body liveOut) l).1 =
      .seq .tick (.seq (.loop (LoopToWord.mkNewCutsetHOL ctxt liveIn) (LoopToWord.compHOL ctxt body l).1
        (LoopToWord.mkNewCutsetHOL ctxt liveOut)) .tick) := by
  simp only [LoopToWord.compHOL]

/-- A successful Loop entry cut is matched by the Word tick and loop cut. -/
theorem loop_entry {C F : Type} {s entry : LoopSemStateFiniteExact 64 F} {liveIn : NumSet}
    (cut : LoopSemStateFiniteExact.cutRes liveIn (none, s) = (none, entry))
    {t : WordSemStateFiniteExact 64 C F} {ctxt : Spt Nat} {retv : WordLocW 64}
    (rel : loopToWordStateRelHOLExact s t) (locals : LoopToWord.localsRelHOL ctxt s.locals t.locals)
    (ret : sptLookup 0 t.locals = some retv) :
    t.clock ≠ 0 ∧ ∃ tcut, cutState (LoopToWord.mkNewCutsetHOL ctxt liveIn, .ln) (decClock t) = some tcut ∧
      loopToWordStateRelHOLExact entry tcut ∧ LoopToWord.localsRelHOL ctxt entry.locals tcut.locals ∧
      sptLookup 0 tcut.locals = some retv := by
  obtain ⟨len, hm, hmd, hsmd, hclock, hbe, hffi, hcur, hlen, htop, hglob, hcode⟩ := rel
  unfold LoopSemStateFiniteExact.cutRes at cut
  simp only at cut
  cases hcs : LoopSemStateFiniteExact.cutState liveIn s with
  | none => simp [hcs] at cut
  | some cs =>
    simp only [hcs] at cut
    have hsub : LoopSemStateFiniteExact.sptSubsetLive liveIn s.locals ∧
        cs = { s with locals := sptInter s.locals liveIn } := by
      unfold LoopSemStateFiniteExact.cutState at hcs
      split at hcs
      · exact ⟨‹_›, (Option.some.inj hcs).symm⟩
      · cases hcs
    obtain ⟨hsub, rfl⟩ := hsub
    by_cases hz : s.clock = 0
    · simp [hz] at cut
    simp only [hz, if_false, Prod.mk.injEq, true_and] at cut
    subst cut
    obtain ⟨env1, hce, hlr⟩ := LoopToWord.wordSemCutEnvMkNewCutsetHOL ctxt liveIn s.locals
      t.locals retv ⟨locals, hsub, ret⟩
    have h0e := (LoopToWord.wordSemCutEnvMkNewCutsetIMPHOL ctxt liveIn t.locals env1 hce).trans ret
    refine ⟨by rw [hclock]; exact hz, { decClock t with locals := env1 }, ?_, ?_, hlr, h0e⟩
    · simp [cutState, decClock, hce]
    · exact ⟨len, hm, hmd, hsmd, by simp [LoopSemStateFiniteExact.decClock, decClock, hclock], hbe, hffi,
        hcur, hlen, htop, hglob, hcode⟩

theorem wordCostLe_loopNext {C F : Type} {s entry middle : LoopSemStateFiniteExact 64 F}
    {liveIn body liveOut result output wb wr}
    (cut : LoopSemStateFiniteExact.cutRes liveIn (none, s) = (none, entry))
    (one : LoopWork entry body (result, middle) wb)
    (again : result = none ∨ result = some (.continue 0))
    (ih1 : WordCostLe C entry body (result, middle) wb)
    (ih2 : WordCostLe C middle (.loop liveIn body liveOut) output wr) :
    WordCostLe C s (.loop liveIn body liveOut) output (3 + wb + wr) := by
  intro ok t ctxt retv l rel locals ret dim notWord acc
  have accBody : ∀ k, sptMem k (accVarsHOL body .ln) → sptMem k ctxt := fun k hk =>
    acc k (by simpa [accVarsHOL] using hk)
  obtain ⟨nz, tcut, hcut, rel1, locals1, ret1⟩ := loop_entry cut rel locals ret
  have okBody : result ≠ some .error := by rcases again with rfl | rfl <;> simp
  obtain ⟨t1, res1, run1, -, rc⟩ := word_run one.sound okBody l rel1 locals1 ret1 dim notWord accBody
  have c1 := ih1 okBody tcut ctxt retv l rel1 locals1 ret1 dim notWord accBody
  have hcont : wordSemContLoop res1 = true ∧ loopToWordStateRelHOLExact middle t1 ∧
      LoopToWord.localsRelHOL ctxt middle.locals t1.locals ∧ sptLookup 0 t1.locals = some retv := by
    rcases again with rfl | rfl
    · obtain ⟨rel2, rfl, ret2, locals2, -, -⟩ := rc
      exact ⟨rfl, rel2, locals2, ret2⟩
    · obtain ⟨rel2, rfl, ret2, locals2, -, -⟩ := rc
      exact ⟨by simp [wordSemContLoop], rel2, locals2, ret2⟩
  obtain ⟨cont, rel2, locals2, ret2⟩ := hcont
  have c2 := ih2 ok t1 ctxt retv l rel2 locals2 ret2 dim notWord acc
  rw [compHOL_loop] at c2 ⊢
  refine Nat.le_trans (tick_loop_tick_upper _ _ _ t nz) ?_
  rw [loop_iteration_cost _ _ _ _ _ hcut run1, if_pos cont]
  by_cases hz : t1.clock = 0
  · simp only [hz, ↓reduceIte]; omega
  · have := tick_loop_tick_lower (LoopToWord.mkNewCutsetHOL ctxt liveIn) (LoopToWord.mkNewCutsetHOL ctxt liveOut)
      (LoopToWord.compHOL ctxt body l).1 t1 hz
    simp only [hz, ↓reduceIte]; omega

theorem wordCostLe_loopBreak {C F : Type} {s entry middle : LoopSemStateFiniteExact 64 F}
    {liveIn body liveOut wb}
    (cut : LoopSemStateFiniteExact.cutRes liveIn (none, s) = (none, entry))
    (one : LoopWork entry body (some (.break 0), middle) wb)
    (ih1 : WordCostLe C entry body (some (.break 0), middle) wb) :
    WordCostLe C s (.loop liveIn body liveOut) (LoopSemStateFiniteExact.cutRes liveOut (none, middle))
      (3 + wb) := by
  intro ok t ctxt retv l rel locals ret dim notWord acc
  have accBody : ∀ k, sptMem k (accVarsHOL body .ln) → sptMem k ctxt := fun k hk =>
    acc k (by simpa [accVarsHOL] using hk)
  obtain ⟨nz, tcut, hcut, rel1, locals1, ret1⟩ := loop_entry cut rel locals ret
  obtain ⟨t1, res1, run1, -, rc⟩ := word_run one.sound (by simp) l rel1 locals1 ret1 dim notWord accBody
  have c1 := ih1 (by simp) tcut ctxt retv l rel1 locals1 ret1 dim notWord accBody
  obtain ⟨-, rfl, -⟩ := rc
  rw [compHOL_loop]
  refine Nat.le_trans (tick_loop_tick_upper _ _ _ t nz) ?_
  rw [loop_iteration_cost _ _ _ _ _ hcut run1]
  simp [wordSemContLoop]
  omega

/-- A body result that leaves the loop is not a Word loop continuation. -/
theorem exit_not_cont {C F : Type} {ctxt : Spt Nat} {retv : WordLocW 64} {tcut t1 : WordSemStateFiniteExact 64 C F}
    {result : Option (LoopSemStateFiniteExact.LoopResultExact 64)} {middle : LoopSemStateFiniteExact 64 F}
    {res1 : Option (WordSemResult 64)}
    (stop : result ≠ none ∧ result ≠ some (.continue 0) ∧ result ≠ some (.break 0))
    (okBody : result ≠ some .error)
    (rc : LoopToWord.CompileCorrect.resultCase ctxt retv tcut result middle res1 t1) :
    wordSemContLoop res1 = false := by
  obtain ⟨h1, h2, h3⟩ := stop
  cases result with
  | none => exact absurd rfl h1
  | some r =>
    cases r with
    | exception v =>
      obtain ⟨-, himp, -⟩ := rc
      by_cases hE : res1 = some .error
      · subst hE; rfl
      · obtain ⟨u1, u2, rfl⟩ := himp hE; rfl
    | «continue» n =>
      obtain ⟨-, rfl, -⟩ := rc
      have : n ≠ 0 := fun h => h2 (by rw [h])
      simp [wordSemContLoop, this]
    | «break» n =>
      obtain ⟨-, rfl, -⟩ := rc
      rfl
    | result v => obtain ⟨-, rfl, -⟩ := rc; rfl
    | timeOut => have h : res1 = some .timeOut := rc; subst h; rfl
    | finalFfi f => have h : res1 = some (.finalFfi f) := rc; subst h; rfl
    | error => exact absurd rfl okBody

theorem wordCostLe_loopExit {C F : Type} {s entry middle : LoopSemStateFiniteExact 64 F}
    {liveIn body liveOut result wb}
    (cut : LoopSemStateFiniteExact.cutRes liveIn (none, s) = (none, entry))
    (one : LoopWork entry body (result, middle) wb)
    (stop : result ≠ none ∧ result ≠ some (.continue 0) ∧ result ≠ some (.break 0))
    (ih1 : WordCostLe C entry body (result, middle) wb) :
    WordCostLe C s (.loop liveIn body liveOut) (LoopSemStateFiniteExact.exitLoop result, middle)
      (3 + wb) := by
  intro ok t ctxt retv l rel locals ret dim notWord acc
  have accBody : ∀ k, sptMem k (accVarsHOL body .ln) → sptMem k ctxt := fun k hk =>
    acc k (by simpa [accVarsHOL] using hk)
  have okBody : result ≠ some .error := by
    intro h; subst h; exact ok (by simp [LoopSemStateFiniteExact.exitLoop])
  obtain ⟨nz, tcut, hcut, rel1, locals1, ret1⟩ := loop_entry cut rel locals ret
  obtain ⟨t1, res1, run1, -, rc⟩ := word_run one.sound okBody l rel1 locals1 ret1 dim notWord accBody
  have c1 := ih1 okBody tcut ctxt retv l rel1 locals1 ret1 dim notWord accBody
  rw [compHOL_loop]
  refine Nat.le_trans (tick_loop_tick_upper _ _ _ t nz) ?_
  rw [loop_iteration_cost _ _ _ _ _ hcut run1]
  rw [exit_not_cont stop okBody rc]
  simp only [Bool.false_eq_true, ↓reduceIte]
  omega

theorem wordCostLe_loopCut {C F : Type} {s cut : LoopSemStateFiniteExact 64 F} {liveIn body liveOut result}
    (stopped : LoopSemStateFiniteExact.cutRes liveIn (none, s) = (some result, cut)) :
    WordCostLe C s (.loop liveIn body liveOut) (some result, cut) 3 := by
  intro ok t ctxt retv l rel locals ret dim notWord acc
  obtain ⟨len, hm, hmd, hsmd, hclock, -⟩ := rel
  have zero : s.clock = 0 := by
    unfold LoopSemStateFiniteExact.cutRes at stopped
    simp only at stopped
    cases hcs : LoopSemStateFiniteExact.cutState liveIn s with
    | none => simp [hcs] at stopped; exact absurd (by rw [← stopped.1]) ok
    | some cs =>
      simp only [hcs] at stopped
      have hcl : cs.clock = s.clock := by
        unfold LoopSemStateFiniteExact.cutState at hcs
        split at hcs
        · cases hcs; rfl
        · cases hcs
      by_cases hz : cs.clock = 0
      · rw [← hcl]; exact hz
      · simp [hz] at stopped
  rw [compHOL_loop, tick_loop_tick_zero _ _ _ t (by rw [hclock]; exact zero)]
  omega

#print axioms wordCostLe_loopNext
#print axioms wordCostLe_loopBreak
#print axioms wordCostLe_loopExit
#print axioms wordCostLe_loopCut
end InitECandidate.Runtime.FineCost
