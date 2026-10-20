import InitECandidate.Runtime.SourceCostLoopWhileBase
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- Executed work of one compiled loop-body iteration: guard code, comparison,
and the selected `Seq body (Continue 0)` or `Break 0` branch. -/
theorem loopWhile_body_work {F : Type} (np : List (HolLoopProg 64)) (le : HolLoopExp 64)
    (tmp : Nat) (l : NumSet) (cC : HolLoopProg 64) (Y st : LoopSemStateFiniteExact 64 F)
    (w : BitVec 64) (a : Nat) (r : LoopResultExact 64) (s' : LoopSemStateFiniteExact 64 F)
    (wbr : Nat)
    (h1 : evaluate (loopNestedSeqHOL np) Y = (none, st))
    (h1v : LoopSemStateFiniteExact.eval st le = some (.word w))
    (supported : loopExpressionCodesWork np = some a)
    (branch : LoopWork (LoopSemStateFiniteExact.setVar tmp (.word w) st)
      (if w = 0 then .break 0 else .seq cC (.continue 0)) (some r, s') wbr) :
    ∃ wB, LoopWork Y (loopNestedSeqHOL (np ++
        [.assign tmp le,
         .ite .notEqual tmp (.imm (0 : BitVec 64)) (.seq cC (.continue 0)) (.break 0) l]))
      (some r, s') wB ∧ wB ≤ a + (1 + loopValueWork le) + (2 + wbr) := by
  have assignRun : evaluate (.assign tmp le) st =
      (none, LoopSemStateFiniteExact.setVar tmp (.word w) st) := by
    rw [evaluate, h1v]
  have assignWork := LoopWork.atom (cost := 1 + loopValueWork le) rfl assignRun
  have chosen : (if Compiler.Encoders.Asm.wordCmpHOL .notEqual w 0 then
      (HolLoopProg.seq cC (.continue 0)) else .break 0) =
      (if w = 0 then .break 0 else .seq cC (.continue 0)) := by
    by_cases hw : w = 0
    · subst hw; simp [Compiler.Encoders.Asm.wordCmpHOL]
    · have h : Compiler.Encoders.Asm.wordCmpHOL .notEqual w 0 = true := by
        simpa [Compiler.Encoders.Asm.wordCmpHOL] using hw
      rw [if_pos h, if_neg hw]
  have iteWork := LoopWork.iteBranch (live := l)
    (s := LoopSemStateFiniteExact.setVar tmp (.word w) st)
    (yes := .seq cC (.continue 0)) (no := .break 0)
    (operator := .notEqual) (register := tmp) (right := .imm (0 : BitVec 64)) (x := w) (y := 0)
    (by simp [LoopSemStateFiniteExact.setVar, sptLookup_sptInsert]) (by rfl)
    (by rw [chosen]; exact branch)
  simp only [LoopSemStateFiniteExact.cutRes] at iteWork
  have tail := LoopWork.seqNext assignWork (LoopWork.seqStop (second := .skip) iteWork)
  obtain ⟨wB, workB, boundB⟩ := loopWork_codes_append np
    [.assign tmp le,
     .ite .notEqual tmp (.imm (0 : BitVec 64)) (.seq cC (.continue 0)) (.break 0) l]
    a Y st (some r, s') _ supported h1 (by simpa only [loopNestedSeqHOL] using tail)
  exact ⟨wB, workB, by omega⟩

/-- Body of a compiled `Seq body (Continue 0)`: the continue is reached only
after a normally completing body. -/
theorem loopWhile_seq_continue_work {F : Type} {cC : HolLoopProg 64}
    {S post : LoopSemStateFiniteExact 64 F} {r : Option (LoopResultExact 64)} {wc : Nat}
    (body : LoopWork S cC (r, post) wc) :
    ∃ w, LoopWork S (.seq cC (.continue 0))
      (match r with | none => some (.continue 0) | some x => some x, post) w ∧ w ≤ wc + 1 := by
  rcases r with _ | x
  · exact ⟨_, LoopWork.seqNext body (LoopWork.atom (cost := 1) rfl (by rw [evaluate])), by omega⟩
  · exact ⟨_, LoopWork.seqStop body, by omega⟩

/-- Shared compiled-loop facts for `While e c`. -/
theorem loopWhile_compile (ctxt : CrepToLoopContextExact) (l : NumSet) (e : CrepExpHOL 64)
    (c : CrepProgHOL 64) {np : List (HolLoopProg 64)} {le : HolLoopExp 64} {tmp : Nat}
    {nl : NumSet} (hC : compileExpHOLExact ctxt (ctxt.vmax + 1) l e = (np, le, tmp, nl)) :
    compileHOLExact ctxt l (.while e c) = .loop l (loopNestedSeqHOL (np ++
      [.assign tmp le,
       .ite .notEqual tmp (.imm (0 : BitVec 64))
         (.seq (compileHOLExact ctxt l c) (.continue 0)) (.break 0) l])) l := by
  rw [compileHOLExact, hC]

/-- False guard: the loop body runs once to its `Break 0` and the loop exits. -/
theorem while_false_loop_paid {F : Type} {ctxt : CrepToLoopContextExact} {l : NumSet}
    {v1 : CrepSemHOLState 64 F} {t : LoopSemStateFiniteExact 64 F}
    {e : CrepExpHOL 64} {c : CrepProgHOL 64}
    (hev : evalCrepSemHOLExp v1 e = some (.word 0)) (rel : CrepLoopRel ctxt l v1 t) :
    LoopPaid ctxt l v1 t (.while e c) (1 + crepNodeWork e) := by
  classical
  obtain ⟨hs, hm, hg, hc, hl⟩ := rel
  have crepRun : evalCrepSemHOLProgExact v1 (.while e c) = (none, v1) := by
    rw [evalCrepSemHOLProgExact_while_holShape, hev]; simp
  rcases hC : compileExpHOLExact ctxt (ctxt.vmax + 1) l e with ⟨np, le, tmp, nl⟩
  obtain ⟨hokA, htA, hlA⟩ := compile_exp_out_rel ctxt (ctxt.vmax + 1) l e np le tmp nl hC
  have hlnl : ∀ k, sptDomain l k → sptDomain nl k :=
    fun k hk => hlA ▸ cut_sets_union_domain_subset _ l hokA k hk
  have htmp : ctxt.vmax < tmp := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) htA
  obtain ⟨codeCost, codeSupported, codeBound⟩ := crep_to_loop_local_work ctxt (ctxt.vmax + 1) l e
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
  have breakWork : LoopWork (LoopSemStateFiniteExact.setVar tmp (.word 0)
      { st with clock := st.clock + 1 })
      (if (0 : BitVec 64) = 0 then .break 0 else .seq (compileHOLExact ctxt l c) (.continue 0))
      (some (.break 0), LoopSemStateFiniteExact.setVar tmp (.word 0)
        { st with clock := st.clock + 1 }) 1 := by
    rw [if_pos rfl]; exact LoopWork.atom (cost := 1) rfl (by rw [evaluate])
  obtain ⟨wB, workB, boundB⟩ := loopWhile_body_work np le tmp l (compileHOLExact ctxt l c) _ _ 0
    codeCost _ _ 1 h1' h1v' codeSupported breakWork
  have loopWork := LoopWork.loopBreak (liveOut := l) hentry workB
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
  have sound := LoopWork.sound loopWork
  refine ⟨ck + 2, 1 + wB, ?_, by omega, ?_⟩
  · rw [sound]; exact loopWork
  · rw [sound, crepRun]
    refine ⟨h1s, h1m, h1g, h1c, rfl, ?_⟩
    exact loopWhile_locals_rel_inter ctxt l v1.locals _
      (loopWhile_locals_rel_insert_of ctxt l nl v1.locals _ st.locals hl h1l hlnl tmp htmp _)

/-- Timeout before an iteration: the loop's entry cut times out. -/
theorem while_timeout_loop_paid {F : Type} {ctxt : CrepToLoopContextExact} {l : NumSet}
    {v1 : CrepSemHOLState 64 F} {t : LoopSemStateFiniteExact 64 F}
    {e : CrepExpHOL 64} {c : CrepProgHOL 64} {w : BitVec 64}
    (hev : evalCrepSemHOLExp v1 e = some (.word w)) (hw : w ≠ 0) (hz : v1.clock = 0)
    (rel : CrepLoopRel ctxt l v1 t) :
    LoopPaid ctxt l v1 t (.while e c) (1 + crepNodeWork e) := by
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
  have loopWork := LoopWork.loopCut (body := loopNestedSeqHOL (np ++
      [.assign tmp le,
       .ite .notEqual tmp (.imm (0 : BitVec 64))
         (.seq (compileHOLExact ctxt l c) (.continue 0)) (.break 0) l])) (liveOut := l) hcut
  rw [← hcomp] at loopWork
  have sound := LoopWork.sound loopWork
  refine ⟨0, 1, ?_, by omega, ?_⟩
  · rw [sound]; exact loopWork
  · rw [sound, crepRun]
    exact ⟨hs, hm, hg, hc, rfl, trivial⟩

#print axioms while_false_loop_paid
#print axioms while_timeout_loop_paid
#print axioms loopWhile_body_work
#print axioms loopWhile_seq_continue_work
end InitECandidate.Runtime.FineCost
