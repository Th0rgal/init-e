import InitECandidate.Runtime.LoopWordCostCallEntry
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact

/-! Tail calls, calls that stop before the callee, and returning calls
without a handler. -/

theorem cutRes_stop_clock {F : Type} {s cut : LoopSemStateFiniteExact 64 F} {live : NumSet} {result}
    (stopped : LoopSemStateFiniteExact.cutRes live (none, s) = (some result, cut))
    (ok : result ≠ .error) : s.clock = 0 := by
  unfold LoopSemStateFiniteExact.cutRes at stopped
  simp only at stopped
  cases hcs : LoopSemStateFiniteExact.cutState live s with
  | none => simp [hcs] at stopped; exact absurd stopped.1.symm ok
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

theorem short_clock {F : Type} {s : LoopSemStateFiniteExact 64 F} {returns target arguments handler output}
    (short : loopCallShort s returns target arguments handler)
    (run : LoopSemStateFiniteExact.evaluate (.call returns target arguments handler) s = output)
    (ok : output.1 ≠ some .error) : s.clock = 0 := by
  rw [LoopSemStateFiniteExact.evaluate] at run
  rcases short with h | ⟨values, hv, h | ⟨env, prog, hf, short⟩⟩
  · simp only [h] at run; subst run; exact absurd rfl ok
  · simp only [hv, h] at run; subst run; exact absurd rfl ok
  · simp only [hv, hf] at run
    rcases short with ⟨rfl, hh | hz⟩ | ⟨names, live, rfl, hnd | ⟨result, cut, hcr⟩⟩
    · simp only [hh, ↓reduceIte] at run; subst run; exact absurd rfl ok
    · exact hz
    · simp only [hnd, not_false_eq_true, ↓reduceIte] at run; subst run; exact absurd rfl ok
    · by_cases hnd : names.Nodup
      · simp only [hnd, not_true_eq_false, ↓reduceIte] at run
        split at run
        · rename_i h; rw [hcr] at h; cases h
        · rw [hcr] at run
          subst run
          exact cutRes_stop_clock hcr (fun h => ok (by rw [h]))
      · simp only [hnd, not_false_eq_true, ↓reduceIte] at run; subst run; exact absurd rfl ok

theorem wordCostLe_callShort {C F : Type} {s : LoopSemStateFiniteExact 64 F}
    {returns target arguments handler output}
    (short : loopCallShort s returns target arguments handler)
    (run : LoopSemStateFiniteExact.evaluate (.call returns target arguments handler) s = output) :
    WordCostLe C s (.call returns target arguments handler) output (1 + arguments.length) := by
  intro ok t ctxt retv l rel locals ret dim notWord acc
  have zero : t.clock = 0 := by
    obtain ⟨len, hm, hmd, hsmd, hclock, -⟩ := rel
    rw [hclock]; exact short_clock short run ok
  rcases returns with _ | ⟨names, live⟩
  · simp only [LoopToWord.compHOL]
    rw [call_cost_zero _ _ _ _ t zero]
    simp [loopWordPrice] <;> omega
  · have noRet : ∀ (R : WordLangProgHOL (BitVec 64)) (h' : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat)),
        ¬ wordCallReturned (.call (some (names.map (LoopToWord.findVarHOL ctxt),
          ((LoopToWord.mkNewCutsetHOL ctxt live, .ln) : WordLangCutsetsHOL), R, l.1, l.2)) target
          (arguments.map (LoopToWord.findVarHOL ctxt)) h') t :=
      fun R h' h => h.1 zero
    rcases handler with _ | ⟨n, p1, p2, liveOut⟩
    · simp only [LoopToWord.compHOL]
      rw [call_cost_zero _ _ _ _ t zero, loopWordPrice, if_neg (noRet _ _)]
      simp
    · simp only [LoopToWord.compHOL]
      rw [wordCost_seq_stop _ _ _ _ (call_eval_zero _ _ _ _ t zero), call_cost_zero _ _ _ _ t zero]
      simp only [loopWordPrice]
      rw [if_neg (noRet _ _)]
      simp

/-- Returned words of the Word callee body are those of the Loop body. -/
theorem retWords_le {C F : Type} {ctxt : Spt Nat} {retv : WordLocW 64} {E t1 : WordSemStateFiniteExact 64 C F}
    {result : Option (LoopSemStateFiniteExact.LoopResultExact 64)} {post : LoopSemStateFiniteExact 64 F}
    {res1 : Option (WordSemResult 64)}
    (rc : LoopToWord.CompileCorrect.resultCase ctxt retv E result post res1 t1) :
    wordRetWords res1 ≤ loopRetWords result := by
  cases result with
  | none => obtain ⟨-, rfl, -⟩ := rc; simp [wordRetWords]
  | some r =>
    cases r with
    | result v => obtain ⟨-, rfl, -⟩ := rc; simp [wordRetWords, loopRetWords]
    | exception v =>
      obtain ⟨-, himp, -⟩ := rc
      by_cases hE : res1 = some .error
      · subst hE; simp [wordRetWords]
      · obtain ⟨u1, u2, rfl⟩ := himp hE; simp [wordRetWords]
    | «break» n => obtain ⟨-, rfl, -⟩ := rc; simp [wordRetWords]
    | «continue» n => obtain ⟨-, rfl, -⟩ := rc; simp [wordRetWords]
    | timeOut => have h : res1 = some .timeOut := rc; subst h; simp [wordRetWords]
    | finalFfi f => have h : res1 = some (.finalFfi f) := rc; subst h; simp [wordRetWords]
    | error => exact rc.elim

theorem wordCostLe_callTail {C F : Type} {s post : LoopSemStateFiniteExact 64 F}
    {target arguments handler values env prog result wb}
    (args : LoopSemStateFiniteExact.getVars arguments s = some values)
    (find : LoopSemStateFiniteExact.findCode target values s.code = some (env, prog))
    (noHandler : handler.isSome = false) (clock : s.clock ≠ 0)
    (ih : WordCostLe C { LoopSemStateFiniteExact.decClock s with locals := env } prog (result, post) wb) :
    WordCostLe C s (.call none target arguments handler) (loopTailExit result post)
      (1 + arguments.length + wb) := by
  intro ok t ctxt retv l rel locals ret dim notWord acc
  have hh : handler = none := by cases handler <;> simp_all
  subst hh
  have okBody : result ≠ some .error := by
    intro h; subst h; exact ok rfl
  have rel' := rel
  obtain ⟨len, hm, hmd, hsmd, hclock, hbe, hffi, hcur, hlen, htop, hglob, hcode⟩ := rel'
  obtain ⟨hwgv, -⟩ := LoopToWord.localsRelHOLGetVars ctxt s t arguments values ⟨locals, args⟩
  obtain ⟨args1, ss1, ctxt1, l1, hwf, h0, hl1, hacc1⟩ :=
    LoopToWord.CompileCorrect.findCode_rel s.code t.code t.stackSize target values env prog retv hcode find
  have hwgv0 : getVars (0 :: arguments.map (LoopToWord.findVarHOL ctxt)) t = some (retv :: values) := by
    simp [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, ret, hwgv]
  have hbad : wordSemBadDestArgs target (0 :: arguments.map (LoopToWord.findVarHOL ctxt)) = false := by
    simp [wordSemBadDestArgs]
  have nz : t.clock ≠ 0 := by rw [hclock]; exact clock
  simp only [LoopToWord.compHOL]
  rw [tail_call_cost _ _ t hwgv0 hbad hwf nz]
  have relBody : loopToWordStateRelHOLExact { LoopSemStateFiniteExact.decClock s with locals := env }
      (callEnv args1 ss1 (decClock t)) := by
    simp only [loopToWordStateRelHOLExact, WordSemStateFiniteExact.callEnv, decClock,
      LoopSemStateFiniteExact.decClock]
    exact ⟨len, hm, hmd, hsmd, by omega, hbe, hffi, hcur, hlen, htop, hglob, hcode⟩
  have := ih okBody (callEnv args1 ss1 (decClock t)) ctxt1 retv l1 relBody hl1 h0 dim notWord hacc1
  simp only [List.length_cons, List.length_map]
  omega

theorem wordCostLe_callRet {C F : Type} {s entry post : LoopSemStateFiniteExact 64 F}
    {names live target arguments values env prog result wb}
    (args : LoopSemStateFiniteExact.getVars arguments s = some values)
    (find : LoopSemStateFiniteExact.findCode target values s.code = some (env, prog))
    (nodup : names.Nodup) (cut : LoopSemStateFiniteExact.cutRes live (none, s) = (none, entry))
    (bodyW : LoopWork { entry with locals := env } prog (result, post) wb)
    (ih : WordCostLe C { entry with locals := env } prog (result, post) wb) :
    WordCostLe C s (.call (some (names, live)) target arguments none) (loopRetExit result post entry names)
      (1 + arguments.length + wb + loopRetWords result) := by
  intro ok t ctxt retv l rel locals ret dim notWord acc
  have okBody : result ≠ some .error := by
    intro h; subst h; exact ok rfl
  have namesCtxt : ∀ k, k ∈ names → sptMem k ctxt := fun k hk => acc k (by
    simp only [accVarsHOL]
    exact (sptMem_sptListInsert_iff k names .ln).mpr (Or.inl hk))
  obtain ⟨args1, ss1, ctxt1, l1, cutEnv, hwgv, hbad, hwf, -, -, hce, nz, -, -, -, hbody, hacc1⟩ :=
    ret_call_entry l rel locals ret namesCtxt args find nodup cut
  obtain ⟨relB, localsB, retB⟩ := hbody none
  simp only [LoopToWord.compHOL]
  rcases hrun : evaluate (LoopToWord.compHOL ctxt1 prog l1).1
    (callEnv args1 ss1 (pushEnv (cutEnv, .ln) none (decClock t))) with ⟨r, m⟩
  refine Nat.le_trans (ret_call_cost_le _ _ _ _ _ _ _ none t hwgv hbad (hwf .skip) hce nz hrun) ?_
  have body := ih okBody _ ctxt1 (.loc l.1 l.2) l1 relB localsB retB dim (by simp [wordSemIsWordLoc]) hacc1
  obtain ⟨t1, res1, he, -, rc⟩ := word_run bodyW.sound okBody l1 relB localsB retB dim
    (by simp [wordSemIsWordLoc]) hacc1
  rw [hrun] at he
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  have words := retWords_le rc
  rcases r with _ | x
  · simp only [List.length_map]; omega
  · cases x <;> simp only [List.length_map] <;> (try split) <;>
      (try simp only [wordCost_skip, loopWordPrice]) <;> omega

#print axioms cutRes_stop_clock
#print axioms short_clock
#print axioms wordCostLe_callShort
#print axioms retWords_le
#print axioms wordCostLe_callTail
#print axioms wordCostLe_callRet
end InitECandidate.Runtime.FineCost
