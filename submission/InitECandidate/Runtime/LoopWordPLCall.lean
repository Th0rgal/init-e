import InitECandidate.Runtime.LoopWordPLBase
import InitECandidate.Runtime.LoopWordPCallBase
import InitECandidate.Runtime.LoopWordCostCall
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact

/-! Label-indexed call rules: short, tail and returning calls without a handler.
Returning calls pay their return-label surcharge, tail calls their target's. -/

section
variable {C F : Type} {wp : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat}
  {lp : LoopPriceL}

theorem tail_price_leL (D : WordDominatesL wp lp) (d : Option Nat) (n : Nat) (args : List Nat)
    (h : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat)) (s : WordSemStateFiniteExact 64 C F)
    (len : args.length = n + 1) :
    wp (.call none d args h) s ≤ lp.base.call + lp.base.argCost n + lp.tail d := by
  have h1 := D.tailCall d args h s
  have h2 := D.tailOk
  have h3 := D.argOk n
  rw [len, Nat.add_sub_cancel] at h1
  omega

theorem ret_price_zero_leL (D : WordDominatesL wp lp) (rets : List Nat) (cut : WordLangCutsetsHOL)
    (rc : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat) (d : Option Nat) (args : List Nat)
    (h : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat)) (s : WordSemStateFiniteExact 64 C F)
    (zero : s.clock = 0) :
    wp (.call (some (rets, cut, rc, l1, l2)) d args h) s ≤ lp.base.call + lp.base.argCost args.length + lp.site (l1, l2) d + lp.retNames rets.length := by
  have h1 := D.retCall rets cut rc l1 l2 d args h s
  rw [if_neg (fun hr => hr.1 zero)] at h1
  have h2 := D.tailOk
  have h3 := D.argOk args.length
  omega

theorem wordCostLePL_callShort (D : WordDominatesL wp lp) {s : LoopSemStateFiniteExact 64 F}
    {returns target arguments handler output}
    (short : loopCallShort s returns target arguments handler)
    {l : Nat × Nat}
    (run : LoopSemStateFiniteExact.evaluate (.call returns target arguments handler) s = output) :
    WordCostLePL C wp s (.call returns target arguments handler) l output
      (lp.base.call + lp.base.argCost arguments.length +
        (match returns with | some (names, _) => lp.site l target + lp.retNames names.length | none => lp.tail target)) := by
  intro ok t ctxt retv rel locals ret dim notWord acc
  obtain ⟨l1, l2⟩ := l
  have zero : t.clock = 0 := by
    obtain ⟨len, hm, hmd, hsmd, hclock, -⟩ := rel
    rw [hclock]; exact short_clock short run ok
  rcases returns with _ | ⟨names, live⟩
  · simp only [LoopToWord.compHOL]
    rw [call_cost_zeroG _ _ _ _ _ t zero]
    exact tail_price_leL D _ _ _ _ t (by simp)
  · rcases handler with _ | ⟨n, p1, p2, liveOut⟩
    · simp only [LoopToWord.compHOL]
      rw [call_cost_zeroG _ _ _ _ _ t zero]
      rw [← List.length_map (f := LoopToWord.findVarHOL ctxt) (as := arguments),
        ← List.length_map (f := LoopToWord.findVarHOL ctxt) (as := names), ← Nat.add_assoc]
      exact ret_price_zero_leL D _ _ _ _ _ _ _ _ t zero
    · simp only [LoopToWord.compHOL]
      rw [wordCost_seq_stop _ _ _ _ (call_eval_zero _ _ _ _ t zero), call_cost_zeroG _ _ _ _ _ t zero,
        D.seqZero, Nat.zero_add]
      rw [← List.length_map (f := LoopToWord.findVarHOL ctxt) (as := arguments),
        ← List.length_map (f := LoopToWord.findVarHOL ctxt) (as := names), ← Nat.add_assoc]
      exact ret_price_zero_leL D _ _ _ _ _ _ _ _ t zero

theorem wordCostLePL_callTail (D : WordDominatesL wp lp) {s post : LoopSemStateFiniteExact 64 F}
    {target arguments handler values env prog result wb}
    (args : LoopSemStateFiniteExact.getVars arguments s = some values)
    (find : LoopSemStateFiniteExact.findCode target values s.code = some (env, prog))
    (noHandler : handler.isSome = false) (clock : s.clock ≠ 0)
    {l : Nat × Nat}
    (ih : WordCostLePL C wp { LoopSemStateFiniteExact.decClock s with locals := env } prog (calleeName target values, 2)
      (result, post) wb) :
    WordCostLePL C wp s (.call none target arguments handler) l (loopTailExit result post)
      (lp.base.call + lp.base.argCost arguments.length + lp.tail target + wb) := by
  intro ok t ctxt retv rel locals ret dim notWord acc
  have hh : handler = none := by cases handler <;> simp_all
  subst hh
  have okBody : result ≠ some .error := by
    intro h; subst h; exact ok rfl
  have rel' := rel
  obtain ⟨len, hm, hmd, hsmd, hclock, hbe, hffi, hcur, hlen, htop, hglob, hcode⟩ := rel'
  obtain ⟨hwgv, -⟩ := LoopToWord.localsRelHOLGetVars ctxt s t arguments values ⟨locals, args⟩
  obtain ⟨args1, ss1, ctxt1, hwf, h0, hl1, hacc1⟩ :=
    findCode_relL s.code t.code t.stackSize target values env prog retv hcode find
  have hwgv0 : getVars (0 :: arguments.map (LoopToWord.findVarHOL ctxt)) t = some (retv :: values) := by
    simp [WordSemStateFiniteExact.getVars, WordSemStateFiniteExact.getVar, ret, hwgv]
  have hbad : wordSemBadDestArgs target (0 :: arguments.map (LoopToWord.findVarHOL ctxt)) = false := by
    simp [wordSemBadDestArgs]
  have nz : t.clock ≠ 0 := by rw [hclock]; exact clock
  simp only [LoopToWord.compHOL]
  rw [tail_call_costG _ _ _ t hwgv0 hbad hwf nz]
  have relBody : loopToWordStateRelHOLExact { LoopSemStateFiniteExact.decClock s with locals := env }
      (callEnv args1 ss1 (decClock t)) := by
    simp only [loopToWordStateRelHOLExact, WordSemStateFiniteExact.callEnv, decClock,
      LoopSemStateFiniteExact.decClock]
    exact ⟨len, hm, hmd, hsmd, by omega, hbe, hffi, hcur, hlen, htop, hglob, hcode⟩
  have body := ih okBody (callEnv args1 ss1 (decClock t)) ctxt1 retv relBody hl1 h0 dim notWord hacc1
  have hp := tail_price_leL D target arguments.length (0 :: arguments.map (LoopToWord.findVarHOL ctxt)) none t
    (by simp)
  omega

theorem wordCostLePL_callRet (D : WordDominatesL wp lp) {s entry post : LoopSemStateFiniteExact 64 F}
    {names live target arguments values env prog result wb}
    (args : LoopSemStateFiniteExact.getVars arguments s = some values)
    (find : LoopSemStateFiniteExact.findCode target values s.code = some (env, prog))
    (nodup : names.Nodup) (cut : LoopSemStateFiniteExact.cutRes live (none, s) = (none, entry))
    {l : Nat × Nat}
    (bodyW : LoopWorkPL lp (calleeName target values, 2) { entry with locals := env } prog (result, post) wb)
    (ih : WordCostLePL C wp { entry with locals := env } prog (calleeName target values, 2) (result, post) wb) :
    WordCostLePL C wp s (.call (some (names, live)) target arguments none) l (loopRetExit result post entry names)
      (lp.base.call + lp.base.argCost arguments.length + lp.site l target + lp.retNames names.length + wb + lp.base.ret * loopRetWords result) := by
  intro ok t ctxt retv rel locals ret dim notWord acc
  obtain ⟨l1, l2⟩ := l
  have okBody : result ≠ some .error := by
    intro h; subst h; exact ok rfl
  have namesCtxt : ∀ k, k ∈ names → sptMem k ctxt := fun k hk => acc k (by
    simp only [accVarsHOL]
    exact (sptMem_sptListInsert_iff k names .ln).mpr (Or.inl hk))
  obtain ⟨args1, ss1, ctxt1, cutEnv, hwgv, hbad, hwf, -, -, hce, nz, -, -, -, hbody, hacc1⟩ :=
    ret_call_entryL (l1, l2) rel locals ret namesCtxt args find nodup cut
  obtain ⟨relB, localsB, retB⟩ := hbody none
  simp only [LoopToWord.compHOL]
  rcases hrun : evaluate (LoopToWord.compHOL ctxt1 prog (calleeName target values, 2)).1
    (callEnv args1 ss1 (pushEnv (cutEnv, .ln) none (decClock t))) with ⟨r, m⟩
  refine Nat.le_trans (ret_call_cost_leG wp _ _ _ _ _ _ _ none t hwgv hbad (hwf .skip) hce nz hrun) ?_
  have body := ih okBody _ ctxt1 (.loc l1 l2) relB localsB retB dim (by simp [wordSemIsWordLoc]) hacc1
  obtain ⟨t1, res1, he, -, rc⟩ := word_run bodyW.sound okBody (calleeName target values, 2) relB localsB retB dim
    (by simp [wordSemIsWordLoc]) hacc1
  rw [hrun] at he
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  have words := retWords_le rc
  have hp := D.retCall (names.map (LoopToWord.findVarHOL ctxt)) (LoopToWord.mkNewCutsetHOL ctxt live, .ln) .skip
    l1 l2 target (arguments.map (LoopToWord.findVarHOL ctxt)) none t
  have hpaid := ret_paid_le D.R (names.map (LoopToWord.findVarHOL ctxt)) (LoopToWord.mkNewCutsetHOL ctxt live, .ln)
    .skip l1 l2 target (arguments.map (LoopToWord.findVarHOL ctxt)) none t hwgv (hwf .skip) hce hrun
  have hR : D.R * wordRetWords r ≤ lp.base.ret * loopRetWords result := Nat.mul_le_mul D.retOk words
  have hA := D.argOk arguments.length
  have hU := D.tailOk
  simp only [List.length_map] at hp hpaid ⊢
  rcases r with _ | x
  · simp only; omega
  · cases x <;> simp only <;> (try split) <;>
      (try simp only [wordCost_skip, D.skipZero]) <;> omega
end


#print axioms wordCostLePL_callShort
#print axioms wordCostLePL_callTail
#print axioms wordCostLePL_callRet
end InitECandidate.Runtime.FineCost
