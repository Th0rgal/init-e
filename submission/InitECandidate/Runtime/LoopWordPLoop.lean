import InitECandidate.Runtime.LoopWordPBase
import InitECandidate.Runtime.LoopWordCostLoop
import InitECandidate.Runtime.LoopWordCostCall
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact

/-! Parametric Loop `loop` rules: `Tick; loop; Tick`. -/

section
variable {C F : Type} {wp : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat}
  {lp : LoopPrice}

theorem tlt_zero (D : WordDominates wp lp) (names exitNames : WordLangNumSetHOL) (body : WordLangProgHOL (BitVec 64))
    (t : WordSemStateFiniteExact 64 C F) (zero : t.clock = 0) :
    wordExecutionCost wp (.seq .tick (.seq (.loop names body exitNames) .tick)) t ≤ D.T := by
  rw [wordExecutionCost_seq, evaluate_tick_unfold, if_pos zero, wordCost_tick, D.seqZero]
  simp only
  have := D.tick t
  omega

theorem tlt_upper (D : WordDominates wp lp) (names exitNames : WordLangNumSetHOL) (body : WordLangProgHOL (BitVec 64))
    (t : WordSemStateFiniteExact 64 C F) (nz : t.clock ≠ 0) :
    wordExecutionCost wp (.seq .tick (.seq (.loop names body exitNames) .tick)) t ≤
      2 * D.T + wordExecutionCost wp (.loop names body exitNames) (decClock t) := by
  rw [wordExecutionCost_seq, evaluate_tick_unfold, if_neg nz, wordCost_tick, D.seqZero]
  simp only
  have h1 := wordCost_seq_le wp (decClock t) (.loop names body exitNames) .tick D.T
    (fun m => by rw [wordCost_tick]; exact D.tick m)
  rw [D.seqZero] at h1
  have h2 := D.tick t
  omega

theorem tlt_lower (D : WordDominates wp lp) (names exitNames : WordLangNumSetHOL) (body : WordLangProgHOL (BitVec 64))
    (t : WordSemStateFiniteExact 64 C F) (nz : t.clock ≠ 0) :
    wordExecutionCost wp (.loop names body exitNames) (decClock t) ≤
      wordExecutionCost wp (.seq .tick (.seq (.loop names body exitNames) .tick)) t := by
  rw [wordExecutionCost_seq, evaluate_tick_unfold, if_neg nz, wordCost_tick, D.seqZero]
  simp only
  rw [wordExecutionCost_seq, D.seqZero]
  omega

theorem loop_iteration_le (D : WordDominates wp lp) (names exitNames : WordLangNumSetHOL)
    (body : WordLangProgHOL (BitVec 64))
    (u entry : WordSemStateFiniteExact 64 C F) (cut : cutState (names, .ln) u = some entry)
    {res1 t1} (run : evaluate body entry = (res1, t1)) :
    wordExecutionCost wp (.loop names body exitNames) u ≤
      D.L + wordExecutionCost wp body entry +
        (if wordSemContLoop res1 then
          (if t1.clock = 0 then 0 else wordExecutionCost wp (.loop names body exitNames) (decClock t1))
         else 0) := by
  have hL := D.loop names body exitNames u
  rw [wordExecutionCost]
  split
  · rename_i h; rw [cut] at h; cases h
  · rename_i e h
    rw [cut] at h
    cases h
    split
    rename_i r m hm
    rw [fix_clock_evaluate, run] at hm
    cases hm
    simp only [wordSemSTOP]
    by_cases hc : wordSemContLoop res1 = true
    · simp only [hc, ↓reduceIte]
      by_cases hz : t1.clock = 0
      · simp only [hz, ↓reduceDIte, ↓reduceIte]; omega
      · simp only [hz, ↓reduceDIte, ↓reduceIte]; omega
    · simp only [hc, Bool.false_eq_true, ↓reduceIte]; omega

theorem wordCostLeP_loopNext (D : WordDominates wp lp) {s entry middle : LoopSemStateFiniteExact 64 F}
    {liveIn body liveOut result output wb wr}
    (cut : LoopSemStateFiniteExact.cutRes liveIn (none, s) = (none, entry))
    (one : LoopWorkP lp entry body (result, middle) wb)
    (again : result = none ∨ result = some (.continue 0))
    (ih1 : WordCostLeP C wp entry body (result, middle) wb)
    (ih2 : WordCostLeP C wp middle (.loop liveIn body liveOut) output wr) :
    WordCostLeP C wp s (.loop liveIn body liveOut) output (lp.iter + wb + wr) := by
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
  have hit := D.iterOk
  refine Nat.le_trans (tlt_upper D _ _ _ t nz) ?_
  refine Nat.le_trans (Nat.add_le_add_left (loop_iteration_le D _ _ _ _ _ hcut run1) _) ?_
  rw [if_pos cont]
  by_cases hz : t1.clock = 0
  · simp only [hz, ↓reduceIte]; omega
  · have := tlt_lower D (LoopToWord.mkNewCutsetHOL ctxt liveIn) (LoopToWord.mkNewCutsetHOL ctxt liveOut)
      (LoopToWord.compHOL ctxt body l).1 t1 hz
    simp only [hz, ↓reduceIte]; omega

theorem wordCostLeP_loopBreak (D : WordDominates wp lp) {s entry middle : LoopSemStateFiniteExact 64 F}
    {liveIn body liveOut wb}
    (cut : LoopSemStateFiniteExact.cutRes liveIn (none, s) = (none, entry))
    (one : LoopWorkP lp entry body (some (.break 0), middle) wb)
    (ih1 : WordCostLeP C wp entry body (some (.break 0), middle) wb) :
    WordCostLeP C wp s (.loop liveIn body liveOut) (LoopSemStateFiniteExact.cutRes liveOut (none, middle))
      (lp.iter + wb) := by
  intro ok t ctxt retv l rel locals ret dim notWord acc
  have accBody : ∀ k, sptMem k (accVarsHOL body .ln) → sptMem k ctxt := fun k hk =>
    acc k (by simpa [accVarsHOL] using hk)
  obtain ⟨nz, tcut, hcut, rel1, locals1, ret1⟩ := loop_entry cut rel locals ret
  obtain ⟨t1, res1, run1, -, rc⟩ := word_run one.sound (by simp) l rel1 locals1 ret1 dim notWord accBody
  have c1 := ih1 (by simp) tcut ctxt retv l rel1 locals1 ret1 dim notWord accBody
  obtain ⟨-, rfl, -⟩ := rc
  have hit := D.iterOk
  rw [compHOL_loop]
  refine Nat.le_trans (tlt_upper D _ _ _ t nz) ?_
  refine Nat.le_trans (Nat.add_le_add_left (loop_iteration_le D _ _ _ _ _ hcut run1) _) ?_
  simp [wordSemContLoop]
  omega

theorem wordCostLeP_loopExit (D : WordDominates wp lp) {s entry middle : LoopSemStateFiniteExact 64 F}
    {liveIn body liveOut result wb}
    (cut : LoopSemStateFiniteExact.cutRes liveIn (none, s) = (none, entry))
    (one : LoopWorkP lp entry body (result, middle) wb)
    (stop : result ≠ none ∧ result ≠ some (.continue 0) ∧ result ≠ some (.break 0))
    (ih1 : WordCostLeP C wp entry body (result, middle) wb) :
    WordCostLeP C wp s (.loop liveIn body liveOut) (LoopSemStateFiniteExact.exitLoop result, middle)
      (lp.iter + wb) := by
  intro ok t ctxt retv l rel locals ret dim notWord acc
  have accBody : ∀ k, sptMem k (accVarsHOL body .ln) → sptMem k ctxt := fun k hk =>
    acc k (by simpa [accVarsHOL] using hk)
  have okBody : result ≠ some .error := by
    intro h; subst h; exact ok (by simp [LoopSemStateFiniteExact.exitLoop])
  obtain ⟨nz, tcut, hcut, rel1, locals1, ret1⟩ := loop_entry cut rel locals ret
  obtain ⟨t1, res1, run1, -, rc⟩ := word_run one.sound okBody l rel1 locals1 ret1 dim notWord accBody
  have c1 := ih1 okBody tcut ctxt retv l rel1 locals1 ret1 dim notWord accBody
  have hit := D.iterOk
  rw [compHOL_loop]
  refine Nat.le_trans (tlt_upper D _ _ _ t nz) ?_
  refine Nat.le_trans (Nat.add_le_add_left (loop_iteration_le D _ _ _ _ _ hcut run1) _) ?_
  rw [exit_not_cont stop okBody rc]
  simp only [Bool.false_eq_true, ↓reduceIte]
  omega

theorem wordCostLeP_loopCut (D : WordDominates wp lp) {s cut : LoopSemStateFiniteExact 64 F}
    {liveIn body liveOut result}
    (stopped : LoopSemStateFiniteExact.cutRes liveIn (none, s) = (some result, cut)) :
    WordCostLeP C wp s (.loop liveIn body liveOut) (some result, cut) lp.iter := by
  intro ok t ctxt retv l rel locals ret dim notWord acc
  obtain ⟨len, hm, hmd, hsmd, hclock, -⟩ := rel
  have zero : s.clock = 0 := cutRes_stop_clock stopped (fun h => ok (by rw [h]))
  have hit := D.iterOk
  rw [compHOL_loop]
  refine Nat.le_trans (tlt_zero D _ _ _ t (by rw [hclock]; exact zero)) ?_
  omega
end

#print axioms wordCostLeP_loopNext
#print axioms wordCostLeP_loopBreak
#print axioms wordCostLeP_loopExit
#print axioms wordCostLeP_loopCut
end InitECandidate.Runtime.FineCost
