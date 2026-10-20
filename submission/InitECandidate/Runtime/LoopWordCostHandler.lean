import InitECandidate.Runtime.LoopWordCostCall
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact

/-! Returning calls with a handler: the continuation after a result and the
handler after an exception. -/

theorem handler_acc {ctxt : Spt Nat} {names : List Nat} {live liveOut : NumSet} {target : Option Nat}
    {arguments : List Nat} {n : Nat} {p1 p2 : HolLoopProg 64}
    (acc : ∀ k, sptMem k (accVarsHOL (.call (some (names, live)) target arguments (some (n, p1, p2, liveOut))) .ln) →
      sptMem k ctxt) :
    (∀ k, k ∈ names → sptMem k ctxt) ∧ sptMem n ctxt ∧
      (∀ k, sptMem k (accVarsHOL p1 .ln) → sptMem k ctxt) ∧
      (∀ k, sptMem k (accVarsHOL p2 .ln) → sptMem k ctxt) := by
  have hdomacc : ∀ k, sptMem k (accVarsHOL (.call (some (names, live)) target arguments
      (some (n, p1, p2, liveOut))) .ln) ↔
      sptMem k (accVarsHOL p1 .ln) ∨ sptMem k (accVarsHOL p2 .ln) ∨ k = n ∨ k ∈ names := by
    intro k
    have e1 := congrFun (accVarsAccHOL p1 (accVarsHOL p2 (sptInsert n () (sptListInsert names .ln)))) k
    have e2 := congrFun (accVarsAccHOL p2 (sptInsert n () (sptListInsert names .ln))) k
    simp only [accVarsHOL]
    change sptDomain _ k ↔ _
    rw [e1]
    change sptMem k _ ∨ sptDomain _ k ↔ _
    rw [e2]
    change sptMem k _ ∨ sptMem k _ ∨ sptMem k _ ↔ _
    rw [sptMem_sptInsert, sptMem_sptListInsert_iff]
    have : ¬ sptMem k (Spt.ln : NumSet) := by simp [sptMem, sptDomain, sptLookup]
    simp [this]
  exact ⟨fun k hk => acc k ((hdomacc k).2 (Or.inr (Or.inr (Or.inr hk)))),
    acc n ((hdomacc n).2 (Or.inr (Or.inr (Or.inl rfl)))),
    fun k hk => acc k ((hdomacc k).2 (Or.inl hk)), fun k hk => acc k ((hdomacc k).2 (Or.inr (Or.inl hk)))⟩

theorem handler_push {C F : Type} (t : WordSemStateFiniteExact 64 C F) (args1 : List (WordLocW 64))
    (ss1 : Option Nat) (result : Spt (WordLocW 64)) (reg : Nat) (code : WordLangProgHOL (BitVec 64))
    (labels : Nat × Nat) :
    (callEnv args1 ss1 (pushEnv (result, Spt.ln) (some (reg, code, labels)) (decClock t))).stack =
      .stackFrame t.localsSize (sptToAList result) [] (some (t.handler, labels.1, labels.2)) :: t.stack := by
  have hx := LoopToWord.envToListLNIMPHOL (width := 64) t.permute _ _ (Prod.eta _).symm
  simp [WordSemStateFiniteExact.callEnv, pushEnv, decClock, hx]

theorem cutRes_ok {F : Type} {live : NumSet}
    {output : Option (LoopSemStateFiniteExact.LoopResultExact 64) × LoopSemStateFiniteExact 64 F}
    (ok : (LoopSemStateFiniteExact.cutRes live output).1 ≠ some .error) : output.1 ≠ some .error := by
  intro h
  apply ok
  rcases output with ⟨r, st⟩
  simp only at h
  subst h
  rfl

theorem wordCostLe_callRetCont {C F : Type} {s entry post : LoopSemStateFiniteExact 64 F}
    {names live target arguments exceptionName handlerProgram continuation liveOut values env prog
      returned wb output wc}
    (args : LoopSemStateFiniteExact.getVars arguments s = some values)
    (find : LoopSemStateFiniteExact.findCode target values s.code = some (env, prog))
    (nodup : names.Nodup) (cut : LoopSemStateFiniteExact.cutRes live (none, s) = (none, entry))
    (bodyW : LoopWork { entry with locals := env } prog (some (.result returned), post) wb)
    (lengths : returned.length = names.length)
    (ih1 : WordCostLe C { entry with locals := env } prog (some (.result returned), post) wb)
    (ih2 : WordCostLe C (LoopSemStateFiniteExact.setVars names returned { post with locals := entry.locals })
      continuation output wc) :
    WordCostLe C s (.call (some (names, live)) target arguments
        (some (exceptionName, handlerProgram, continuation, liveOut)))
      (LoopSemStateFiniteExact.cutRes liveOut output) (1 + arguments.length + wb + returned.length + wc) := by
  intro ok t ctxt retv l rel locals ret dim notWord acc
  obtain ⟨namesCtxt, -, -, accCont⟩ := handler_acc acc
  obtain ⟨args1, ss1, ctxt1, l1, cutEnv, hwgv, hbad, hwf, -, -, hce, nz, hentry, hlr, h0r, hbody, hacc1⟩ :=
    ret_call_entry l rel locals ret namesCtxt args find nodup cut
  subst hentry
  rcases hc1 : LoopToWord.compHOL ctxt handlerProgram (l.1, l.2 + 1) with ⟨w1, lab1⟩
  rcases hc2 : LoopToWord.compHOL ctxt continuation lab1 with ⟨w2, lab2⟩
  have unfold : (LoopToWord.compHOL ctxt (.call (some (names, live)) target arguments
      (some (exceptionName, handlerProgram, continuation, liveOut))) l).1 =
      .seq (.call (some (names.map (LoopToWord.findVarHOL ctxt), (LoopToWord.mkNewCutsetHOL ctxt live, .ln), w2, l))
        target (arguments.map (LoopToWord.findVarHOL ctxt))
        (some (LoopToWord.findVarHOL ctxt exceptionName, w1, lab2))) .tick := by
    unfold LoopToWord.compHOL; simp only [hc1, hc2]
  rw [unfold]
  refine Nat.le_trans (wordCost_seq_le _ _ _ _ 1 fun m => by rw [wordCost_tick]; simp [loopWordPrice]) ?_
  obtain ⟨relB, localsB, retB⟩ := hbody (some (LoopToWord.findVarHOL ctxt exceptionName, w1, lab2))
  obtain ⟨t1, res1, he, -, rc⟩ := word_run bodyW.sound (by simp) l1 relB localsB retB dim
    (by simp [wordSemIsWordLoc]) hacc1
  have body := ih1 (by simp) _ ctxt1 (.loc l.1 l.2) l1 relB localsB retB dim (by simp [wordSemIsWordLoc]) hacc1
  simp only [loopWordPrice, Nat.zero_add]
  refine Nat.le_trans (Nat.add_le_add_right (ret_call_cost_le _ _ _ _ _ _ _ _ t hwgv hbad (hwf w2) hce nz he) 1) ?_
  obtain ⟨hst, rfl, hstk, -⟩ := rc
  have hpop : popEnv t1 = some { t1 with
      locals := sptUnion (sptFromAList []) (sptFromAList (sptToAList cutEnv)),
      stack := t.stack, localsSize := t.localsSize, handler := t.handler } := by
    unfold popEnv
    rw [hstk, handler_push]
  simp only [hpop]
  have h0ns : 0 ∉ names.map (LoopToWord.findVarHOL ctxt) := by
    intro hmem
    obtain ⟨n, hn', h⟩ := List.mem_map.mp hmem
    exact LoopToWord.findVarHOL_ne_zero ctxt s.locals t.locals n ⟨namesCtxt n hn', locals⟩ h
  have relC : loopToWordStateRelHOLExact
      (LoopSemStateFiniteExact.setVars names returned
        { post with locals := (LoopSemStateFiniteExact.decClock { s with locals := sptInter s.locals live }).locals })
      (setVars (names.map (LoopToWord.findVarHOL ctxt)) returned { t1 with
        locals := sptUnion (sptFromAList []) (sptFromAList (sptToAList cutEnv)),
        stack := t.stack, localsSize := t.localsSize, handler := t.handler }) := by
    obtain ⟨len', e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := hst
    simp only [loopToWordStateRelHOLExact, setVars, LoopSemStateFiniteExact.setVars]
    exact ⟨len', e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩
  have localsC : LoopToWord.localsRelHOL ctxt
      (LoopSemStateFiniteExact.setVars names returned
        { post with locals := (LoopSemStateFiniteExact.decClock { s with locals := sptInter s.locals live }).locals }).locals
      (setVars (names.map (LoopToWord.findVarHOL ctxt)) returned { t1 with
        locals := sptUnion (sptFromAList []) (sptFromAList (sptToAList cutEnv)),
        stack := t.stack, localsSize := t.localsSize, handler := t.handler }).locals := by
    have h := LoopToWord.localsRelHOLAlistInsertToAList ctxt names returned
      (sptInter s.locals live) cutEnv ⟨hlr, namesCtxt⟩
    simp only [setVars, LoopSemStateFiniteExact.setVars, sptUnion, sptFromAList]
    exact h
  have retC : sptLookup 0 (setVars (names.map (LoopToWord.findVarHOL ctxt)) returned { t1 with
        locals := sptUnion (sptFromAList []) (sptFromAList (sptToAList cutEnv)),
        stack := t.stack, localsSize := t.localsSize, handler := t.handler }).locals = some retv := by
    simp only [setVars]
    rw [LoopSemStateFiniteExact.sptLookup_sptAlistInsert_not_mem 0 _ _ _ h0ns]
    simpa [sptUnion, sptFromAList, sptLookup_sptFromAList_sptToAList] using h0r
  have cont := ih2 (cutRes_ok ok) _ ctxt retv lab1 relC localsC retC dim notWord accCont
  rw [hc2] at cont
  simp only [List.length_map, wordRetWords] at cont ⊢
  omega

theorem wordCostLe_callHandle {C F : Type} {s entry post : LoopSemStateFiniteExact 64 F}
    {names live target arguments exceptionName handlerProgram continuation liveOut values env prog
      exn wb output wh}
    (args : LoopSemStateFiniteExact.getVars arguments s = some values)
    (find : LoopSemStateFiniteExact.findCode target values s.code = some (env, prog))
    (nodup : names.Nodup) (cut : LoopSemStateFiniteExact.cutRes live (none, s) = (none, entry))
    (bodyW : LoopWork { entry with locals := env } prog (some (.exception exn), post) wb)
    (ih1 : WordCostLe C { entry with locals := env } prog (some (.exception exn), post) wb)
    (ih2 : WordCostLe C (LoopSemStateFiniteExact.setVar exceptionName exn { post with locals := entry.locals })
      handlerProgram output wh) :
    WordCostLe C s (.call (some (names, live)) target arguments
        (some (exceptionName, handlerProgram, continuation, liveOut)))
      (LoopSemStateFiniteExact.cutRes liveOut output) (2 + arguments.length + wb + wh) := by
  intro ok t ctxt retv l rel locals ret dim notWord acc
  obtain ⟨namesCtxt, nameCtxt, accHandler, -⟩ := handler_acc acc
  obtain ⟨args1, ss1, ctxt1, l1, cutEnv, hwgv, hbad, hwf, -, -, hce, nz, hentry, hlr, h0r, hbody, hacc1⟩ :=
    ret_call_entry l rel locals ret namesCtxt args find nodup cut
  subst hentry
  rcases hc1 : LoopToWord.compHOL ctxt handlerProgram (l.1, l.2 + 1) with ⟨w1, lab1⟩
  rcases hc2 : LoopToWord.compHOL ctxt continuation lab1 with ⟨w2, lab2⟩
  have unfold : (LoopToWord.compHOL ctxt (.call (some (names, live)) target arguments
      (some (exceptionName, handlerProgram, continuation, liveOut))) l).1 =
      .seq (.call (some (names.map (LoopToWord.findVarHOL ctxt), (LoopToWord.mkNewCutsetHOL ctxt live, .ln), w2, l))
        target (arguments.map (LoopToWord.findVarHOL ctxt))
        (some (LoopToWord.findVarHOL ctxt exceptionName, w1, lab2))) .tick := by
    unfold LoopToWord.compHOL; simp only [hc1, hc2]
  rw [unfold]
  refine Nat.le_trans (wordCost_seq_le _ _ _ _ 1 fun m => by rw [wordCost_tick]; simp [loopWordPrice]) ?_
  obtain ⟨relB, localsB, retB⟩ := hbody (some (LoopToWord.findVarHOL ctxt exceptionName, w1, lab2))
  obtain ⟨t1, res1, he, -, rc⟩ := word_run bodyW.sound (by simp) l1 relB localsB retB dim
    (by simp [wordSemIsWordLoc]) hacc1
  have body := ih1 (by simp) _ ctxt1 (.loc l.1 l.2) l1 relB localsB retB dim (by simp [wordSemIsWordLoc]) hacc1
  simp only [loopWordPrice, Nat.zero_add]
  refine Nat.le_trans (Nat.add_le_add_right (ret_call_cost_le _ _ _ _ _ _ _ _ t hwgv hbad (hwf w2) hce nz he) 1) ?_
  obtain ⟨hst, -, hj⟩ := rc
  have hpush := handler_push t args1 ss1 cutEnv (LoopToWord.findVarHOL ctxt exceptionName) w1 lab2
  have hjx : jumpExc { t1 with
      stack := (callEnv args1 ss1 (pushEnv (cutEnv, Spt.ln)
        (some (LoopToWord.findVarHOL ctxt exceptionName, w1, lab2)) (decClock t))).stack,
      handler := (callEnv args1 ss1 (pushEnv (cutEnv, Spt.ln)
        (some (LoopToWord.findVarHOL ctxt exceptionName, w1, lab2)) (decClock t))).handler } =
      some ({ t1 with
        locals := sptUnion (sptFromAList []) (sptFromAList (sptToAList cutEnv)),
        stack := t.stack, localsSize := t.localsSize, handler := t.handler }, lab2.1, lab2.2) := by
    have hhand : (callEnv args1 ss1 (pushEnv (cutEnv, Spt.ln)
        (some (LoopToWord.findVarHOL ctxt exceptionName, w1, lab2)) (decClock t))).handler = t.stack.length := by
      simp [WordSemStateFiniteExact.callEnv, pushEnv, decClock]
    unfold jumpExc
    simp only [hpush, hhand]
    rw [if_pos (by simp)]
    have hfull : wordSemLastN (t.stack.length + 1)
        (.stackFrame t.localsSize (sptToAList cutEnv) [] (some (t.handler, lab2.1, lab2.2)) :: t.stack) =
        .stackFrame t.localsSize (sptToAList cutEnv) [] (some (t.handler, lab2.1, lab2.2)) :: t.stack := by
      simp only [wordSemLastN, List.reverse_cons]
      rw [List.take_of_length_le (by simp)]
      simp
    rw [hfull]
  obtain ⟨rfl, hR0⟩ := hj _ _ _ hjx
  have hl1loc : t1.locals = sptUnion (sptFromAList []) (sptFromAList (sptToAList cutEnv)) := by rw [← hR0]
  have hhn0 := LoopToWord.findVarHOL_ne_zero ctxt s.locals t.locals exceptionName ⟨nameCtxt, locals⟩
  have relH : loopToWordStateRelHOLExact
      (LoopSemStateFiniteExact.setVar exceptionName exn
        { post with locals := (LoopSemStateFiniteExact.decClock { s with locals := sptInter s.locals live }).locals })
      (setVar (LoopToWord.findVarHOL ctxt exceptionName) exn t1) := by
    obtain ⟨len', e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩ := hst
    simp only [loopToWordStateRelHOLExact, setVar, LoopSemStateFiniteExact.setVar]
    exact ⟨len', e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11⟩
  have localsH : LoopToWord.localsRelHOL ctxt
      (LoopSemStateFiniteExact.setVar exceptionName exn
        { post with locals := (LoopSemStateFiniteExact.decClock { s with locals := sptInter s.locals live }).locals }).locals
      (setVar (LoopToWord.findVarHOL ctxt exceptionName) exn t1).locals := by
    have h := LoopToWord.localsRelHOLAlistInsertToAList ctxt [exceptionName] [exn]
      (sptInter s.locals live) cutEnv ⟨hlr, fun k hk => by
        simp only [List.mem_singleton] at hk
        subst hk
        exact nameCtxt⟩
    simp only [setVar, LoopSemStateFiniteExact.setVar, hl1loc, sptUnion, sptFromAList]
    simp only [LoopSemStateFiniteExact.sptAlistInsert, List.map_cons, List.map_nil] at h
    exact h
  have retH : sptLookup 0 (setVar (LoopToWord.findVarHOL ctxt exceptionName) exn t1).locals = some retv := by
    simp only [setVar, hl1loc]
    rw [sptLookup_sptInsert_ne _ _ _ _ (Ne.symm hhn0)]
    simpa [sptUnion, sptFromAList, sptLookup_sptFromAList_sptToAList] using h0r
  have handle := ih2 (cutRes_ok ok) _ ctxt retv (l.1, l.2 + 1) relH localsH retH dim notWord accHandler
  rw [hc1] at handle
  simp only [List.length_map, wordRetWords] at handle ⊢
  omega

#print axioms wordCostLe_callRetCont
#print axioms wordCostLe_callHandle
end InitECandidate.Runtime.FineCost
