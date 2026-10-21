import InitECandidate.Runtime.CrepLoopTransferG
import InitECandidate.Runtime.SourceCostLoopWhile
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- Executed work of one compiled loop-body iteration: guard code, comparison,
and the selected `Seq body (Continue 0)` or `Break 0` branch. -/
theorem loopWhile_body_workG (P : LoopPricingG) (f : Nat) {F : Type} (np : List (HolLoopProg 64)) (le : HolLoopExp 64)
    (tmp : Nat) (l : NumSet) (cC : HolLoopProg 64) (Y st : LoopSemStateFiniteExact 64 F)
    (w : BitVec 64) (a : Nat) (r : LoopResultExact 64) (s' : LoopSemStateFiniteExact 64 F)
    (wbr : Nat)
    (h1 : evaluate (loopNestedSeqHOL np) Y = (none, st))
    (h1v : LoopSemStateFiniteExact.eval st le = some (.word w))
    (supported : P.A.works np = some a)
    (branch : LoopWorkG P.L f (LoopSemStateFiniteExact.setVar tmp (.word w) st)
      (if w = 0 then .break 0 else .seq cC (.continue 0)) (some r, s') wbr) :
    ∃ wB, LoopWorkG P.L f Y (loopNestedSeqHOL (np ++
        [.assign tmp le,
         .ite .notEqual tmp (.imm (0 : BitVec 64)) (.seq cC (.continue 0)) (.break 0) l]))
      (some r, s') wB ∧ wB ≤ a + P.vp le + (P.L.ite + wbr) := by
  have assignRun : evaluate (.assign tmp le) st =
      (none, LoopSemStateFiniteExact.setVar tmp (.word w) st) := by
    rw [evaluate, h1v]
  obtain ⟨ka, hka, hkale⟩ := P.assignOk tmp le
  have assignWork := LoopWorkG.atom (f := f) hka assignRun
  have chosen : (if Compiler.Encoders.Asm.wordCmpHOL .notEqual w 0 then
      (HolLoopProg.seq cC (.continue 0)) else .break 0) =
      (if w = 0 then .break 0 else .seq cC (.continue 0)) := by
    by_cases hw : w = 0
    · subst hw; simp [Compiler.Encoders.Asm.wordCmpHOL]
    · have h : Compiler.Encoders.Asm.wordCmpHOL .notEqual w 0 = true := by
        simpa [Compiler.Encoders.Asm.wordCmpHOL] using hw
      rw [if_pos h, if_neg hw]
  have iteWork := LoopWorkG.iteBranch (live := l)
    (s := LoopSemStateFiniteExact.setVar tmp (.word w) st)
    (yes := .seq cC (.continue 0)) (no := .break 0)
    (operator := .notEqual) (register := tmp) (right := .imm (0 : BitVec 64)) (x := w) (y := 0)
    (by simp [LoopSemStateFiniteExact.setVar, sptLookup_sptInsert]) (by rfl)
    (by rw [chosen]; exact branch)
  simp only [LoopSemStateFiniteExact.cutRes] at iteWork
  have tail := LoopWorkG.seqNext assignWork (LoopWorkG.seqStop (second := .skip) iteWork)
  obtain ⟨wB, workB, boundB⟩ := P.A.run_append f np
    [.assign tmp le,
     .ite .notEqual tmp (.imm (0 : BitVec 64)) (.seq cC (.continue 0)) (.break 0) l]
    a Y st (some r, s') _ supported h1 (by simpa only [loopNestedSeqHOL] using tail)
  exact ⟨wB, workB, by omega⟩

/-- Body of a compiled `Seq body (Continue 0)`: the continue is reached only
after a normally completing body. -/
theorem loopWhile_seq_continue_workG (P : LoopPricingG) (f : Nat) {F : Type} {cC : HolLoopProg 64}
    {S post : LoopSemStateFiniteExact 64 F} {r : Option (LoopResultExact 64)} {wc : Nat}
    (body : LoopWorkG P.L f S cC (r, post) wc) :
    ∃ w, LoopWorkG P.L f S (.seq cC (.continue 0))
      (loopContinueResult r, post) w ∧ w ≤ wc + P.contC := by
  obtain ⟨kc, hkc, hkcle⟩ := P.contOk 0
  rcases r with _ | x
  · exact ⟨_, LoopWorkG.seqNext body (LoopWorkG.atom hkc
      (by rw [evaluate]; rfl)), by omega⟩
  · exact ⟨_, LoopWorkG.seqStop body, by omega⟩

/-- False guard: the loop body runs once to its `Break 0` and the loop exits. -/
theorem while_false_loop_paidG (P : LoopPricingG) (f : Nat) {K : StmtK} (hb : P.L.iter + P.L.ite + P.breakC ≤ K.wh) (hc : P.L.iter + P.L.ite + P.contC ≤ K.wh) {F : Type} {ctxt : CrepToLoopContextExact} {l : NumSet}
    {v1 : CrepSemHOLState 64 F} {t : LoopSemStateFiniteExact 64 F}
    {e : CrepExpHOL 64} {c : CrepProgHOL 64}
    (hev : evalCrepSemHOLExp v1 e = some (.word 0)) (rel : CrepLoopRel ctxt l v1 t) :
    LoopPaidG P.L f ctxt l v1 t (.while e c) (K.wh + P.price e) := by
  have := hb
  have := hc
  classical
  obtain ⟨hs, hm, hg, hc, hl⟩ := rel
  have crepRun : evalCrepSemHOLProgExact v1 (.while e c) = (none, v1) := by
    rw [evalCrepSemHOLProgExact_while_holShape, hev]; simp
  rcases hC : compileExpHOLExact ctxt (ctxt.vmax + 1) l e with ⟨np, le, tmp, nl⟩
  obtain ⟨hokA, htA, hlA⟩ := compile_exp_out_rel ctxt (ctxt.vmax + 1) l e np le tmp nl hC
  have hlnl : ∀ k, sptDomain l k → sptDomain nl k :=
    fun k hk => hlA ▸ cut_sets_union_domain_subset _ l hokA k hk
  have htmp : ctxt.vmax < tmp := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) htA
  obtain ⟨codeCost, codeSupported, codeBound⟩ := P.exprOk ctxt (ctxt.vmax + 1) l e
  rw [hC] at codeSupported codeBound
  try dsimp only at codeSupported codeBound
  have hcomp := loopWhile_compile ctxt l e c hC
  have hsub : LoopSemStateFiniteExact.sptSubsetLive l t.locals := hl.2.2.1
  obtain ⟨ck, st, h1, h1v, h1s, h1m, h1g, h1c, h1l⟩ :=
    crepToLoop_comp_exp_preserves_eval v1 e (.word 0) { t with locals := sptInter t.locals l }
      ctxt (ctxt.vmax + 1) l np le tmp nl
      ⟨hev, hs, hm, hg, hc, loopWhile_locals_rel_inter ctxt l v1.locals t.locals hl, hC,
        Nat.lt_succ_self _⟩
  have hentry : LoopSemStateFiniteExact.cutRes l (none, { t with clock := t.clock + (ck + 2) }) =
      (none, { t with locals := sptInter t.locals l, clock := t.clock + (ck + 1) }) := by
    rw [LoopSemStateFiniteExact.cutRes]
    simp only
    rw [LoopSemStateFiniteExact.cutState_of_subset l { t with clock := t.clock + (ck + 2) } hsub]
    simp only [LoopSemStateFiniteExact.decClock, show ¬ t.clock + (ck + 2) = 0 by omega, if_false]
    simp only [Prod.mk.injEq, true_and]
    congr 1
  have h1' : evaluate (loopNestedSeqHOL np)
      { t with locals := sptInter t.locals l, clock := t.clock + (ck + 1) } =
        (none, { st with clock := st.clock + 1 }) := by
    have := LoopSemStateFiniteExact.evaluate_add_clock_eq _ _ _ _ 1 h1 (by simp)
    simpa [Nat.add_assoc] using this
  have h1v' : LoopSemStateFiniteExact.eval { st with clock := st.clock + 1 } le =
      some (.word 0) := by
    rw [LoopSemStateFiniteExact.eval_upd_clock_eq]; simpa [wlabWlocExact] using h1v
  obtain ⟨kb, hkb, hkble⟩ := P.breakOk 0
  have breakWork : LoopWorkG P.L f (LoopSemStateFiniteExact.setVar tmp (.word 0)
      { st with clock := st.clock + 1 })
      (if (0 : BitVec 64) = 0 then .break 0 else .seq (compileHOLExact ctxt l c) (.continue 0))
      (some (.break 0), LoopSemStateFiniteExact.setVar tmp (.word 0)
        { st with clock := st.clock + 1 }) kb := by
    rw [if_pos rfl]; exact LoopWorkG.atom hkb (by rw [evaluate])
  obtain ⟨wB, workB, boundB⟩ := loopWhile_body_workG P f np le tmp l (compileHOLExact ctxt l c) _ _ 0
    codeCost _ _ kb h1' h1v' codeSupported breakWork
  have loopWork := LoopWorkG.loopBreak (liveOut := l) hentry workB
  have hS : LoopSemStateFiniteExact.sptSubsetLive l
      (LoopSemStateFiniteExact.setVar tmp (.word 0) { st with clock := st.clock + 1 }).locals :=
    fun k hk => (sptMem_sptInsert k tmp _ _).mpr (Or.inr (h1l.2.2.1 k (hlnl k hk)))
  have hexit : LoopSemStateFiniteExact.cutRes l
      (none, LoopSemStateFiniteExact.setVar tmp (.word 0) { st with clock := st.clock + 1 }) =
      (none, { st with locals := sptInter (sptInsert tmp (.word 0) st.locals) l }) := by
    rw [LoopSemStateFiniteExact.cutRes]
    simp only
    rw [LoopSemStateFiniteExact.cutState_of_subset l _ hS]
    simp [LoopSemStateFiniteExact.decClock, LoopSemStateFiniteExact.setVar]
  rw [hexit, ← hcomp] at loopWork
  have sound := LoopWorkG.sound loopWork
  refine ⟨ck + 2, P.L.iter + wB, ?_, by omega, ?_⟩
  · rw [sound]; exact loopWork
  · rw [sound, crepRun]
    refine ⟨h1s, h1m, h1g, h1c, rfl, ?_⟩
    exact loopWhile_locals_rel_inter ctxt l v1.locals _
      (loopWhile_locals_rel_insert_of ctxt l nl v1.locals _ st.locals hl h1l hlnl tmp htmp _)

/-- Timeout before an iteration: the loop's entry cut times out. -/
theorem while_timeout_loop_paidG (P : LoopPricingG) (f : Nat) {K : StmtK} (hb : P.L.iter + P.L.ite + P.breakC ≤ K.wh) (hc : P.L.iter + P.L.ite + P.contC ≤ K.wh) {F : Type} {ctxt : CrepToLoopContextExact} {l : NumSet}
    {v1 : CrepSemHOLState 64 F} {t : LoopSemStateFiniteExact 64 F}
    {e : CrepExpHOL 64} {c : CrepProgHOL 64} {w : BitVec 64}
    (hev : evalCrepSemHOLExp v1 e = some (.word w)) (hw : w ≠ 0) (hz : v1.clock = 0)
    (rel : CrepLoopRel ctxt l v1 t) :
    LoopPaidG P.L f ctxt l v1 t (.while e c) (K.wh + P.price e) := by
  have := hb
  have := hc
  classical
  obtain ⟨hs, hm, hg, hc, hl⟩ := rel
  have crepRun : evalCrepSemHOLProgExact v1 (.while e c) =
      (some .timeOut, CrepSemHOLState.emptyLocals v1) := by
    rw [evalCrepSemHOLProgExact_while_holShape, hev]
    simp only [ne_eq, hz, if_true]
    rw [if_pos hw]
  rcases hC : compileExpHOLExact ctxt (ctxt.vmax + 1) l e with ⟨np, le, tmp, nl⟩
  have hcomp := loopWhile_compile ctxt l e c hC
  have hsub : LoopSemStateFiniteExact.sptSubsetLive l t.locals := hl.2.2.1
  have ht0 : t.clock = 0 := hs.2.2.1 ▸ hz
  have hcut : LoopSemStateFiniteExact.cutRes l (none, { t with clock := t.clock + 0 }) =
      (some .timeOut, { t with clock := t.clock + 0, locals := .ln }) := by
    rw [LoopSemStateFiniteExact.cutRes]
    simp only
    rw [LoopSemStateFiniteExact.cutState_of_subset l { t with clock := t.clock + 0 } hsub]
    simp [ht0]
  have loopWork := LoopWorkG.loopCut (L := P.L) (f := f) (body := loopNestedSeqHOL (np ++
      [.assign tmp le,
       .ite .notEqual tmp (.imm (0 : BitVec 64))
         (.seq (compileHOLExact ctxt l c) (.continue 0)) (.break 0) l])) (liveOut := l) hcut
  rw [← hcomp] at loopWork
  have sound := LoopWorkG.sound loopWork
  refine ⟨0, P.L.iter, ?_, by omega, ?_⟩
  · rw [sound]; exact loopWork
  · rw [sound, crepRun]
    exact ⟨hs, hm, hg, hc, rfl, trivial⟩

/-- Shared iteration prelude: entry cut, guard materialization at the
decremented clock, and the body's simulation premises. -/
structure LoopWhileIterG (P : LoopPricingG) {F : Type} (ctxt : CrepToLoopContextExact) (l : NumSet)
    (v1 : CrepSemHOLState 64 F) (t : LoopSemStateFiniteExact 64 F)
    (e : CrepExpHOL 64) (c : CrepProgHOL 64) (w : BitVec 64) : Prop where
  out : ∃ (np : List (HolLoopProg 64)) (le : HolLoopExp 64) (tmp : Nat) (a ck : Nat)
      (st : LoopSemStateFiniteExact 64 F),
    compileHOLExact ctxt l (.while e c) = .loop l (loopNestedSeqHOL (np ++
      [.assign tmp le,
       .ite .notEqual tmp (.imm (0 : BitVec 64))
         (.seq (compileHOLExact ctxt l c) (.continue 0)) (.break 0) l])) l ∧
    P.A.works np = some a ∧ a + P.vp le ≤ P.price e ∧
    (∀ k, LoopSemStateFiniteExact.cutRes l (none, { t with clock := t.clock + (ck + k) }) =
      (none, { t with locals := sptInter t.locals l, clock := t.clock - 1 + (ck + k) })) ∧
    (∀ k, evaluate (loopNestedSeqHOL np)
      { t with locals := sptInter t.locals l, clock := t.clock - 1 + (ck + k) } =
        (none, { st with clock := st.clock + k })) ∧
    (∀ k, LoopSemStateFiniteExact.eval { st with clock := st.clock + k } le = some (.word w)) ∧
    CrepLoopRel ctxt l (decClockCrepSemHOL v1) (LoopSemStateFiniteExact.setVar tmp (.word w) st)

theorem loopWhile_iterG (P : LoopPricingG) {F : Type} {ctxt : CrepToLoopContextExact} {l : NumSet}
    {v1 : CrepSemHOLState 64 F} {t : LoopSemStateFiniteExact 64 F}
    {e : CrepExpHOL 64} {c : CrepProgHOL 64} {w : BitVec 64}
    (hev : evalCrepSemHOLExp v1 e = some (.word w)) (hz : v1.clock ≠ 0)
    (rel : CrepLoopRel ctxt l v1 t) : LoopWhileIterG P ctxt l v1 t e c w := by
  classical
  obtain ⟨hs, hm, hg, hc, hl⟩ := rel
  rcases hC : compileExpHOLExact ctxt (ctxt.vmax + 1) l e with ⟨np, le, tmp, nl⟩
  obtain ⟨hokA, htA, hlA⟩ := compile_exp_out_rel ctxt (ctxt.vmax + 1) l e np le tmp nl hC
  have hlnl : ∀ k, sptDomain l k → sptDomain nl k :=
    fun k hk => hlA ▸ cut_sets_union_domain_subset _ l hokA k hk
  have htmp : ctxt.vmax < tmp := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) htA
  obtain ⟨codeCost, codeSupported, codeBound⟩ := P.exprOk ctxt (ctxt.vmax + 1) l e
  rw [hC] at codeSupported codeBound
  try dsimp only at codeSupported codeBound
  have hsub : LoopSemStateFiniteExact.sptSubsetLive l t.locals := hl.2.2.1
  obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6, hs7⟩ := hs
  have htz : t.clock ≠ 0 := hs3 ▸ hz
  have hev' : evalCrepSemHOLExp (decClockCrepSemHOL v1) e = some (.word w) := by
    simp only [decClockCrepSemHOL, evalCrepSemHOLExp_upd_clock_eq, hev]
  have hsD : crepToLoopStateRelExact (decClockCrepSemHOL v1)
      { t with locals := sptInter t.locals l, clock := t.clock - 1 } :=
    ⟨hs1, hs2, by simp [decClockCrepSemHOL, hs3], hs4, hs5, hs6, hs7⟩
  obtain ⟨ck, st, h1, h1v, h1s, h1m, h1g, h1c, h1l⟩ :=
    crepToLoop_comp_exp_preserves_eval (decClockCrepSemHOL v1) e (.word w)
      { t with locals := sptInter t.locals l, clock := t.clock - 1 }
      ctxt (ctxt.vmax + 1) l np le tmp nl
      ⟨hev', hsD, hm, hg, hc, loopWhile_locals_rel_inter ctxt l v1.locals t.locals hl, hC,
        Nat.lt_succ_self _⟩
  refine ⟨⟨np, le, tmp, codeCost, ck, st, loopWhile_compile ctxt l e c hC, codeSupported,
    codeBound, ?_, ?_, ?_, ⟨h1s, h1m, h1g, h1c, ?_⟩⟩⟩
  · intro k
    rw [LoopSemStateFiniteExact.cutRes]
    simp only
    rw [LoopSemStateFiniteExact.cutState_of_subset l { t with clock := t.clock + (ck + k) } hsub]
    simp only [LoopSemStateFiniteExact.decClock, show ¬ t.clock + (ck + k) = 0 by omega, if_false]
    simp only [Prod.mk.injEq, true_and]
    congr 1
    omega
  · intro k
    have := LoopSemStateFiniteExact.evaluate_add_clock_eq _ _ _ _ k h1 (by simp)
    simpa [Nat.add_assoc] using this
  · intro k
    rw [LoopSemStateFiniteExact.eval_upd_clock_eq]; simpa [wlabWlocExact] using h1v
  · exact loopWhile_locals_rel_insert_of ctxt l nl v1.locals _ st.locals
      (loopWhile_locals_rel_inter ctxt l v1.locals t.locals hl) h1l hlnl tmp htmp _

/-- A normally completing (or continuing) iteration followed by the rest of
the loop. -/
theorem while_loop_loop_paidG (P : LoopPricingG) (f : Nat) {K : StmtK} (hb : P.L.iter + P.L.ite + P.breakC ≤ K.wh) (hc : P.L.iter + P.L.ite + P.contC ≤ K.wh) {F : Type} {ctxt : CrepToLoopContextExact} {l : NumSet}
    {v1 middle : CrepSemHOLState 64 F} {t : LoopSemStateFiniteExact 64 F}
    {e : CrepExpHOL 64} {c : CrepProgHOL 64} {w : BitVec 64}
    {result : Option (CrepResultHOLExact 64)} {wb wr : Nat}
    (hev : evalCrepSemHOLExp v1 e = some (.word w)) (hw : w ≠ 0) (hz : v1.clock ≠ 0)
    (hbody : evalCrepSemHOLProgExact (decClockCrepSemHOL v1) c = (result, middle))
    (again : result = none ∨ result = some (.continue 0))
    (rel : CrepLoopRel ctxt l v1 t)
    (ihBody : ∀ u', CrepLoopRel ctxt l (decClockCrepSemHOL v1) u' →
      LoopPaidG P.L f ctxt l (decClockCrepSemHOL v1) u' c wb)
    (ihRest : ∀ u', CrepLoopRel ctxt l middle u' → LoopPaidG P.L f ctxt l middle u' (.while e c) wr) :
    LoopPaidG P.L f ctxt l v1 t (.while e c) (K.wh + P.price e + wb + wr) := by
  have := hb
  have := hc
  classical
  have crepRun : evalCrepSemHOLProgExact v1 (.while e c) =
      evalCrepSemHOLProgExact middle (.while e c) := by
    rw [evalCrepSemHOLProgExact_while_holShape, hev]
    simp only [ne_eq, hz, if_false]
    rw [if_pos hw, hbody]
    rcases again with rfl | rfl <;> rfl
  obtain ⟨⟨np, le, tmp, a, ck, st, hcomp, supported, codeBound, hentryK, h1k, h1v, bodyRel⟩⟩ :=
    loopWhile_iterG P (c := c) hev hz rel
  obtain ⟨ck', wb', workBody, boundBody, relBody⟩ := ihBody _ bodyRel
  rw [hbody] at relBody
  rcases hb : evaluate (compileHOLExact ctxt l c)
      { LoopSemStateFiniteExact.setVar tmp (.word w) st with
        clock := (LoopSemStateFiniteExact.setVar tmp (.word w) st).clock + ck' } with ⟨res1', t1⟩
  rw [hb] at workBody relBody
  obtain ⟨h2s, h2m, h2g, h2c, h2r, h2l⟩ := relBody
  try dsimp only at h2s h2m h2g h2c h2r h2l
  have bodyNotTimeout : res1' ≠ some .timeOut := by
    rw [h2r]; rcases again with rfl | rfl <;> simp [resultToLoop]
  have h2l' : crepToLoopLocalsRelExact ctxt l middle.locals t1.locals := by
    rcases again with rfl | rfl <;> exact h2l
  obtain ⟨ck'', wr', workRest, boundRest, relRest⟩ := ihRest t1 ⟨h2s, h2m, h2g, h2c, h2l'⟩
  rw [hcomp] at workRest relRest
  have lifted := LoopWorkG.add_clock workBody ck'' bodyNotTimeout
  simp only [] at lifted
  rw [loopWhile_setVar_clock] at lifted
  obtain ⟨wbr, branchWork, branchBound⟩ := loopWhile_seq_continue_workG P f lifted
  have contResult : loopContinueResult res1' = some (.continue 0) := by
    rw [h2r]; rcases again with rfl | rfl <;> rfl
  rw [contResult] at branchWork
  obtain ⟨wB, workB, boundB⟩ := loopWhile_body_workG P f np le tmp l (compileHOLExact ctxt l c) _
    { st with clock := st.clock + (ck' + ck'') } w a (.continue 0) _ wbr (h1k (ck' + ck''))
    (h1v (ck' + ck'')) supported (by rw [if_neg hw]; exact branchWork)
  have loopWork := LoopWorkG.loopNext (hentryK (ck' + ck'')) workB (Or.inr rfl) workRest
  rw [← hcomp] at loopWork
  have sound := LoopWorkG.sound loopWork
  refine ⟨ck + (ck' + ck''), P.L.iter + wB + wr', ?_, by omega, ?_⟩
  · rw [sound]; exact loopWork
  · rw [sound, crepRun]
    rw [hcomp]
    exact relRest

/-- An iteration whose body exits the loop (break) or the enclosing code. -/
theorem while_stop_loop_paidG (P : LoopPricingG) (f : Nat) {K : StmtK} (hb : P.L.iter + P.L.ite + P.breakC ≤ K.wh) (hc : P.L.iter + P.L.ite + P.contC ≤ K.wh) {F : Type} {ctxt : CrepToLoopContextExact} {l : NumSet}
    {v1 middle : CrepSemHOLState 64 F} {t : LoopSemStateFiniteExact 64 F}
    {e : CrepExpHOL 64} {c : CrepProgHOL 64} {w : BitVec 64}
    {result : Option (CrepResultHOLExact 64)} {wb : Nat}
    (hev : evalCrepSemHOLExp v1 e = some (.word w)) (hw : w ≠ 0) (hz : v1.clock ≠ 0)
    (hbody : evalCrepSemHOLProgExact (decClockCrepSemHOL v1) c = (result, middle))
    (stop : result ≠ none ∧ result ≠ some (.continue 0))
    (ok : (evalCrepSemHOLProgExact v1 (.while e c)).1 ≠ some .error)
    (rel : CrepLoopRel ctxt l v1 t)
    (ihBody : ∀ u', CrepLoopRel ctxt l (decClockCrepSemHOL v1) u' →
      LoopPaidG P.L f ctxt l (decClockCrepSemHOL v1) u' c wb) :
    LoopPaidG P.L f ctxt l v1 t (.while e c) (K.wh + P.price e + wb) := by
  have := hb
  have := hc
  classical
  obtain ⟨r, rfl⟩ := Option.ne_none_iff_exists'.mp stop.1
  have crepRun : evalCrepSemHOLProgExact v1 (.while e c) =
      (if r = .break 0 then (none, middle) else (exitLoopCrepResult (some r), middle)) := by
    rw [evalCrepSemHOLProgExact_while_holShape, hev]
    simp only [ne_eq, hz, if_false]
    rw [if_pos hw, hbody]
    by_cases hb0 : r = .break 0
    · subst hb0; simp
    · rw [if_neg hb0]
      cases r with
      | «continue» n => cases n with
        | zero => exact absurd rfl stop.2
        | succ n => rfl
      | «break» n => cases n with
        | zero => exact absurd rfl hb0
        | succ n => rfl
      | _ => rfl
  obtain ⟨⟨np, le, tmp, a, ck, st, hcomp, supported, codeBound, hentryK, h1k, h1v, bodyRel⟩⟩ :=
    loopWhile_iterG P (c := c) hev hz rel
  obtain ⟨ck', wb', workBody, boundBody, relBody⟩ := ihBody _ bodyRel
  rw [hbody] at relBody
  rcases hb : evaluate (compileHOLExact ctxt l c)
      { LoopSemStateFiniteExact.setVar tmp (.word w) st with
        clock := (LoopSemStateFiniteExact.setVar tmp (.word w) st).clock + ck' } with ⟨res1', t1⟩
  rw [hb] at workBody relBody
  obtain ⟨h2s, h2m, h2g, h2c, h2r, h2l⟩ := relBody
  try dsimp only at h2s h2m h2g h2c h2r h2l
  have notError : r ≠ .error := by
    intro h
    subst h
    apply ok
    rw [crepRun]
    simp [exitLoopCrepResult]
  obtain ⟨x, hx⟩ : ∃ x, res1' = some x := by
    cases r <;> simp only [resultToLoop] at h2r <;> exact ⟨_, h2r⟩
  subst hx
  by_cases hr1 : r = .break 0
  · subst hr1
    have hx : x = .break 0 := by simpa [resultToLoop] using h2r
    subst hx
    have h2l' : crepToLoopLocalsRelExact ctxt l middle.locals t1.locals := h2l
    have lifted := LoopWorkG.add_clock workBody 1 (by simp)
    simp only [] at lifted
    rw [loopWhile_setVar_clock] at lifted
    obtain ⟨wbr, branchWork, branchBound⟩ := loopWhile_seq_continue_workG P f lifted
    simp only [loopContinueResult] at branchWork
    obtain ⟨wB, workB, boundB⟩ := loopWhile_body_workG P f np le tmp l (compileHOLExact ctxt l c) _
      { st with clock := st.clock + (ck' + 1) } w a (.break 0) _ wbr (h1k (ck' + 1))
      (h1v (ck' + 1)) supported (by rw [if_neg hw]; exact branchWork)
    have loopWork := LoopWorkG.loopBreak (liveOut := l) (hentryK (ck' + 1)) workB
    have hsub1 : LoopSemStateFiniteExact.sptSubsetLive l t1.locals := h2l'.2.2.1
    have hexit : LoopSemStateFiniteExact.cutRes l (none, { t1 with clock := t1.clock + 1 }) =
        (none, { t1 with locals := sptInter t1.locals l }) := by
      rw [LoopSemStateFiniteExact.cutRes]
      simp only
      rw [LoopSemStateFiniteExact.cutState_of_subset l { t1 with clock := t1.clock + 1 } hsub1]
      simp [LoopSemStateFiniteExact.decClock]
    rw [hexit, ← hcomp] at loopWork
    have sound := LoopWorkG.sound loopWork
    refine ⟨ck + (ck' + 1), P.L.iter + wB, ?_, by omega, ?_⟩
    · rw [sound]; exact loopWork
    · rw [sound, crepRun, if_pos rfl]
      exact ⟨h2s, h2m, h2g, h2c, rfl, loopWhile_locals_rel_inter ctxt l middle.locals t1.locals h2l'⟩
  · have hx0 : x ≠ .continue 0 := by
      intro h; subst h; cases r <;> simp_all [resultToLoop]
    have hx1 : x ≠ .break 0 := by
      intro h; subst h; cases r <;> simp_all [resultToLoop]
    have rewritten : LoopWorkG P.L f { LoopSemStateFiniteExact.setVar tmp (.word w) st with
        clock := (LoopSemStateFiniteExact.setVar tmp (.word w) st).clock + ck' }
        (compileHOLExact ctxt l c) (some x, t1) wb' := workBody
    have stateEq : ({ LoopSemStateFiniteExact.setVar tmp (.word w) st with
        clock := (LoopSemStateFiniteExact.setVar tmp (.word w) st).clock + ck' } :
        LoopSemStateFiniteExact 64 F) =
        LoopSemStateFiniteExact.setVar tmp (.word w) { st with clock := st.clock + ck' } := by
      simp [LoopSemStateFiniteExact.setVar]
    rw [stateEq] at rewritten
    obtain ⟨wbr, branchWork, branchBound⟩ := loopWhile_seq_continue_workG P f rewritten
    simp only [loopContinueResult] at branchWork
    obtain ⟨wB, workB, boundB⟩ := loopWhile_body_workG P f np le tmp l (compileHOLExact ctxt l c) _
      { st with clock := st.clock + ck' } w a x _ wbr (by simpa using h1k ck')
      (h1v ck') supported (by rw [if_neg hw]; exact branchWork)
    have loopWork := LoopWorkG.loopExit (liveOut := l) (hentryK ck') workB
      ⟨by simp, by simpa using hx0, by simpa using hx1⟩
    rw [← hcomp] at loopWork
    have sound := LoopWorkG.sound loopWork
    refine ⟨ck + ck', P.L.iter + wB, ?_, by omega, ?_⟩
    · simpa using (by rw [sound]; exact loopWork : _)
    · rw [sound, crepRun, if_neg hr1]
      refine ⟨h2s, h2m, h2g, h2c, ?_, loopWhile_localsResultRel_exitLoop ctxt l _ _ r h2l⟩
      rw [h2r]
      exact loopWhile_resultToLoop_exitLoop r (fun h => stop.2 (by rw [h])) hr1

#print axioms loopWhile_iterG
#print axioms while_loop_loop_paidG
#print axioms while_stop_loop_paidG
#print axioms while_false_loop_paidG
#print axioms while_timeout_loop_paidG
end InitECandidate.Runtime.FineCost
