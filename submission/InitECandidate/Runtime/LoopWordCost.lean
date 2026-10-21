import InitECandidate.Runtime.LoopWordCostLoop
import InitECandidate.Runtime.LoopWordCostHandler
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact

/-! The Loop-to-Word cost transfer for every `LoopWork` run. -/

/-- A returning call with a handler whose body neither returns a value of the
right length nor raises: the body stops the call (timeout or FFI exit). -/
theorem wordCostLe_callRetPlain {C F : Type} {s entry post : LoopSemStateFiniteExact 64 F}
    {names live target arguments n p1 p2 liveOut values env prog result wb}
    (args : LoopSemStateFiniteExact.getVars arguments s = some values)
    (find : LoopSemStateFiniteExact.findCode target values s.code = some (env, prog))
    (nodup : names.Nodup) (cut : LoopSemStateFiniteExact.cutRes live (none, s) = (none, entry))
    (bodyW : LoopWork { entry with locals := env } prog (result, post) wb)
    (plain : loopRetPlain result names (some (n, p1, p2, liveOut)))
    (ih : WordCostLe C { entry with locals := env } prog (result, post) wb) :
    WordCostLe C s (.call (some (names, live)) target arguments (some (n, p1, p2, liveOut)))
      (loopRetExit result post entry names) (1 + arguments.length + wb + loopRetWords result) := by
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
  simp only [loopWordPrice, Nat.zero_add]
  refine Nat.le_trans (ret_call_cost_le _ _ _ _ _ _ _ _ t hwgv hbad (hwf w2) hce nz he) ?_
  have hres : res1 = some .timeOut ∨ ∃ f, res1 = some (.finalFfi f) := by
    rcases stops with rfl | ⟨f, rfl⟩
    · exact Or.inl rc
    · exact Or.inr ⟨f, rc⟩
  rcases hres with rfl | ⟨f, rfl⟩ <;> simp only [List.length_map, wordRetWords] <;> omega

theorem cutRes_error {F : Type} (live : NumSet)
    (output : Option (LoopSemStateFiniteExact.LoopResultExact 64) × LoopSemStateFiniteExact 64 F)
    (h : output.1 = some .error) : (LoopSemStateFiniteExact.cutRes live output).1 = some .error := by
  rcases output with ⟨r, st⟩
  simp only at h
  subst h
  rfl

#print axioms wordCostLe_callRetPlain
end InitECandidate.Runtime.FineCost
