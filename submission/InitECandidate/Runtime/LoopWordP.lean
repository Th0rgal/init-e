import InitECandidate.Runtime.LoopWordPLoop
import InitECandidate.Runtime.LoopWordPHandler
import InitECandidate.Runtime.LoopWordCost
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact

/-! The price-parametric Loop-to-Word transfer for every `LoopWorkP` run. -/

section
variable {C F : Type} {wp : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat}
  {lp : LoopPrice}

theorem wordCostLeP_callRetPlain (D : WordDominates wp lp) {s entry post : LoopSemStateFiniteExact 64 F}
    {names live target arguments n p1 p2 liveOut values env prog result wb}
    (args : LoopSemStateFiniteExact.getVars arguments s = some values)
    (find : LoopSemStateFiniteExact.findCode target values s.code = some (env, prog))
    (nodup : names.Nodup) (cut : LoopSemStateFiniteExact.cutRes live (none, s) = (none, entry))
    (bodyW : LoopWorkP lp { entry with locals := env } prog (result, post) wb)
    (plain : loopRetPlain result names (some (n, p1, p2, liveOut)))
    (ih : WordCostLeP C wp { entry with locals := env } prog (result, post) wb) :
    WordCostLeP C wp s (.call (some (names, live)) target arguments (some (n, p1, p2, liveOut)))
      (loopRetExit result post entry names) (lp.call + lp.argCost arguments.length + wb + lp.ret * loopRetWords result) := by
  intro ok t ctxt retv l rel locals ret dim notWord acc
  have stops : result = some .timeOut ∨ ∃ f, result = some (.finalFfi f) := by
    rcases result with _ | (_ | _ | _ | _ | v | e | _)
    all_goals first
      | exact absurd rfl ok
      | exact Or.inl rfl
      | exact Or.inr ⟨_, rfl⟩
      | skip
    · simp only [loopRetExit] at ok
      split at ok
      · exact absurd rfl ok
      · simp [loopRetPlain] at plain
        exact absurd plain (by assumption)
    · simp [loopRetPlain] at plain
  obtain ⟨namesCtxt, -, -, -⟩ := handler_acc acc
  obtain ⟨args1, ss1, ctxt1, l1, cutEnv, hwgv, hbad, hwf, hne, hnd, hce, nz, -, -, -, hbody, hacc1⟩ :=
    ret_call_entry l rel locals ret namesCtxt args find nodup cut
  rcases hc1 : LoopToWord.compHOL ctxt p1 (l.1, l.2 + 1) with ⟨w1, lab1⟩
  rcases hc2 : LoopToWord.compHOL ctxt p2 lab1 with ⟨w2, lab2⟩
  have unfold : (LoopToWord.compHOL ctxt (.call (some (names, live)) target arguments
      (some (n, p1, p2, liveOut))) l).1 =
      .seq (.call (some (names.map (LoopToWord.findVarHOL ctxt), (LoopToWord.mkNewCutsetHOL ctxt live, .ln), w2, l))
        target (arguments.map (LoopToWord.findVarHOL ctxt))
        (some (LoopToWord.findVarHOL ctxt n, w1, lab2))) .tick := by
    unfold LoopToWord.compHOL; simp only [hc1, hc2]
  rw [unfold]
  obtain ⟨relB, localsB, retB⟩ := hbody (some (LoopToWord.findVarHOL ctxt n, w1, lab2))
  have okBody : result ≠ some .error := by rcases stops with rfl | ⟨f, rfl⟩ <;> simp
  obtain ⟨t1, res1, he, -, rc⟩ := word_run bodyW.sound okBody l1 relB localsB retB dim
    (by simp [wordSemIsWordLoc]) hacc1
  have body := ih okBody _ ctxt1 (.loc l.1 l.2) l1 relB localsB retB dim (by simp [wordSemIsWordLoc]) hacc1
  have hres0 : res1 = some .timeOut ∨ ∃ f, res1 = some (.finalFfi f) := by
    rcases stops with rfl | ⟨f, rfl⟩
    · exact Or.inl rc
    · exact Or.inr ⟨f, rc⟩
  rw [wordCost_seq_stop _ _ _ _ (ret_call_eval_stop _ _ _ _ _ _ _ _ t hwgv hbad (hwf w2) hne hnd hce nz he hres0)]
  rw [D.seqZero, Nat.zero_add]
  refine Nat.le_trans (ret_call_cost_leG wp _ _ _ _ _ _ _ _ t hwgv hbad (hwf w2) hce nz he) ?_
  have hp := D.retCall (names.map (LoopToWord.findVarHOL ctxt)) (LoopToWord.mkNewCutsetHOL ctxt live, .ln) w2
    l.1 l.2 target (arguments.map (LoopToWord.findVarHOL ctxt)) (some (LoopToWord.findVarHOL ctxt n, w1, lab2)) t
  have hpaid := ret_paid_le D.R (names.map (LoopToWord.findVarHOL ctxt)) (LoopToWord.mkNewCutsetHOL ctxt live, .ln)
    w2 l.1 l.2 target (arguments.map (LoopToWord.findVarHOL ctxt)) (some (LoopToWord.findVarHOL ctxt n, w1, lab2))
    t hwgv (hwf w2) hce he
  have hA := D.argOk arguments.length
  have hU := D.tailOk
  have hres : res1 = some .timeOut ∨ ∃ f, res1 = some (.finalFfi f) := by
    rcases stops with rfl | ⟨f, rfl⟩
    · exact Or.inl rc
    · exact Or.inr ⟨f, rc⟩
  rcases hres with rfl | ⟨f, rfl⟩ <;> simp only [List.length_map, wordRetWords, Nat.mul_zero] at hp hpaid ⊢ <;> omega

/-- Parametric Loop-to-Word executed cost: for any Word price dominated by the
Loop price `lp`, from any Word state related as in the pinned `compile_correct`,
the compiled program's executed Word work is at most the `LoopWorkP lp` of the
same non-error run. -/
theorem loop_to_word_costP (D : WordDominates wp lp) {s : LoopSemStateFiniteExact 64 F} {p : HolLoopProg 64}
    {output w} (work : LoopWorkP lp s p output w) : WordCostLeP C wp s p output w := by
  induction work with
  | atom leaf run => exact wordCostLeP_atom D leaf
  | mark inner ih => exact wordCostLeP_mark ih
  | seqNext one two ih1 ih2 => exact wordCostLeP_seqNext D one ih1 ih2
  | seqStop one ih => exact wordCostLeP_seqStop D one ih
  | iteBranch lhs rhs branch ih => exact wordCostLeP_iteBranch D lhs rhs ih (cutRes_error _ _)
  | iteInvalid invalid => intro ok; exact absurd rfl ok
  | loopNext cut one again rest ih1 ih2 => exact wordCostLeP_loopNext D cut one again ih1 ih2
  | loopBreak cut one ih => exact wordCostLeP_loopBreak D cut one ih
  | loopExit cut one stop ih => exact wordCostLeP_loopExit D cut one stop ih
  | loopCut stopped => exact wordCostLeP_loopCut D stopped
  | callShort short run => exact wordCostLeP_callShort D short run
  | callTail args find noHandler clock body ih => exact wordCostLeP_callTail D args find noHandler clock ih
  | @callRet s names live target arguments handler values env prog entry result post wb args find nodup cut
      body plain ih =>
    rcases handler with _ | ⟨n, p1, p2, liveOut⟩
    · exact wordCostLeP_callRet D args find nodup cut body ih
    · exact wordCostLeP_callRetPlain D args find nodup cut body plain ih
  | callRetCont args find nodup cut body lengths cont ih1 ih2 =>
    exact wordCostLeP_callRetCont D args find nodup cut body lengths ih1 ih2
  | callHandle args find nodup cut body handle ih1 ih2 =>
    exact wordCostLeP_callHandle D args find nodup cut body ih1 ih2
end

#print axioms wordCostLeP_callRetPlain
#print axioms loop_to_word_costP
end InitECandidate.Runtime.FineCost
