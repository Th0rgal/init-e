import InitECandidate.Runtime.SourceCostLoopTransfer
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact Flapjack.Pancake.CrepToLoop.Proofs.NCompileCorrect

/-- Generated expression code followed by an arbitrary continuation: the
code's actual prefix is paid by its allowance. -/
theorem loopWork_codes_append {F : Type} : ∀ (codes rest : List (HolLoopProg 64)) (c : Nat)
    (s middle : LoopSemStateFiniteExact 64 F)
    (output : Option (LoopResultExact 64) × LoopSemStateFiniteExact 64 F) (wr : Nat),
    loopExpressionCodesWork codes = some c →
    evaluate (loopNestedSeqHOL codes) s = (none, middle) →
    LoopWork middle (loopNestedSeqHOL rest) output wr →
    ∃ w, LoopWork s (loopNestedSeqHOL (codes ++ rest)) output w ∧ w ≤ c + wr
  | [], rest, c, s, middle, output, wr, h, run, tail => by
    simp [loopExpressionCodesWork] at h
    subst h
    rw [loopNestedSeqHOL, evaluate] at run
    cases run
    exact ⟨wr, by simpa using tail, by omega⟩
  | head :: codes, rest, c, s, middle, output, wr, h, run, tail => by
    simp only [loopExpressionCodesWork] at h
    cases ha : loopExpressionCodeWork head <;> cases hb : loopExpressionCodesWork codes <;>
      simp_all
    rename_i a b
    subst h
    rw [loopNestedSeqHOL, evaluate_seq] at run
    rcases hx : evaluate head s with ⟨r1, s1⟩
    rw [hx] at run
    rcases r1 with _ | r1
    · simp only at run
      obtain ⟨wx, workx, boundx⟩ := loopBounded_of_codeWork head a ha F s
      rw [hx] at workx
      obtain ⟨w', work', bound'⟩ := loopWork_codes_append codes rest b s1 middle output wr hb run tail
      refine ⟨wx + w', ?_, by omega⟩
      rw [loopNestedSeqHOL]
      exact LoopWork.seqNext workx work'
    · simp at run

/-- The pinned If case's locals-relation step after materializing the guard. -/
theorem if_guard_locals {F : Type} {context : CrepToLoopContextExact} {live nl : NumSet}
    {t : CrepSemHOLState 64 F} {u st : LoopSemStateFiniteExact 64 F} {e : CrepExpHOL 64}
    {np : List (HolLoopProg 64)} {le : HolLoopExp 64} {tmp : Nat} {w : BitVec 64}
    (hC : compileExpHOLExact context (context.vmax + 1) live e = (np, le, tmp, nl))
    (hl : crepToLoopLocalsRelExact context live t.locals u.locals)
    (h1l : crepToLoopLocalsRelExact context nl t.locals st.locals) :
    crepToLoopLocalsRelExact context live t.locals
      (LoopSemStateFiniteExact.setVar tmp (.word w) st).locals := by
  obtain ⟨hokA, htA, hlA⟩ := compile_exp_out_rel context (context.vmax + 1) live e np le tmp nl hC
  refine ⟨h1l.1, h1l.2.1, fun k hk => ?_, fun vn val hval => ?_⟩
  · have hnl : sptDomain nl k := hlA ▸ cut_sets_union_domain_subset _ live hokA k hk
    exact (sptMem_sptInsert k tmp _ _).mpr (Or.inr (h1l.2.2.1 k hnl))
  · obtain ⟨n, hn1, hn2, _⟩ := hl.2.2.2 vn val hval
    obtain ⟨n', hn1', _, hn3'⟩ := h1l.2.2.2 vn val hval
    have hnn : n' = n := Option.some.inj (hn1'.symm.trans hn1)
    subst hnn
    have hle := h1l.2.1 vn n' hn1'
    refine ⟨n', hn1', hn2, ?_⟩
    simp only [LoopSemStateFiniteExact.setVar, sptLookup_sptInsert]
    rw [if_neg (by omega)]
    exact hn3'

/-- Conditional transfer: guard materialization, the comparison, the selected
compiled branch (with the original relations) and the join. -/
theorem ite_loop_paid (P : LoopPricing) {F : Type} {context : CrepToLoopContextExact} {live : NumSet}
    {t : CrepSemHOLState 64 F} {u : LoopSemStateFiniteExact 64 F}
    {condition : CrepExpHOL 64} {yes no : CrepProgHOL 64} {word : BitVec 64} {wb : Nat}
    (guard : evalCrepSemHOLExp t condition = some (.word word))
    (ok : (evalCrepSemHOLProgExact t (.ite condition yes no)).1 ≠ some .error)
    (rel : CrepLoopRel context live t u)
    (ih : ∀ u', CrepLoopRel context live t u' →
      LoopPaid context live t u' (if word ≠ 0 then yes else no) wb) :
    LoopPaid context live t u (.ite condition yes no) (P.unit + P.price condition + wb) := by
  have unitOk := P.unitOk
  classical
  have crepRun : evalCrepSemHOLProgExact t (.ite condition yes no) =
      evalCrepSemHOLProgExact t (if word ≠ 0 then yes else no) := by
    rw [evalCrepSemHOLProgExact_ite_holShape, guard]
  rcases hC : compileExpHOLExact context (context.vmax + 1) live condition with ⟨np, le, tmp, nl⟩
  obtain ⟨ck, st, h1, h1v, h1s, h1m, h1g, h1c, h1l⟩ :=
    crepToLoop_comp_exp_preserves_eval t condition (.word word) u context (context.vmax + 1)
      live np le tmp nl ⟨guard, rel.state, rel.memory, rel.globals, rel.code, rel.locals, hC,
        Nat.lt_succ_self _⟩
  obtain ⟨codeCost, codeSupported, codeBound⟩ :=
    P.exprOk context (context.vmax + 1) live condition
  rw [hC] at codeSupported codeBound
  simp only [] at codeSupported codeBound
  have hl' := if_guard_locals (w := word) hC rel.locals h1l
  obtain ⟨e', wl', work', bound', rel'⟩ :=
    ih (LoopSemStateFiniteExact.setVar tmp (.word word) st) ⟨h1s, h1m, h1g, h1c, hl'⟩
  have hcomp : compileHOLExact context live (.ite condition yes no) =
      loopNestedSeqHOL (np ++
        [.assign tmp le,
         .ite .notEqual tmp (.imm (0 : BitVec 64))
           (compileHOLExact context live yes) (compileHOLExact context live no) live]) := by
    rw [compileHOLExact, hC]
  have chosen : (if Compiler.Encoders.Asm.wordCmpHOL .notEqual word 0 then
      compileHOLExact context live yes else compileHOLExact context live no) =
      compileHOLExact context live (if word ≠ 0 then yes else no) := by
    by_cases hw : word = 0
    · subst hw; simp [Compiler.Encoders.Asm.wordCmpHOL]
    · have h1 : Compiler.Encoders.Asm.wordCmpHOL .notEqual word 0 = true := by
        simpa [Compiler.Encoders.Asm.wordCmpHOL] using hw
      rw [if_pos h1]
      simp only [ne_eq, hw, not_false_eq_true, if_true]
  -- the tail after the guard code, from `st` at any clock extension `k`
  have tailWork : ∀ (k : Nat) (output : Option (LoopResultExact 64) ×
        LoopSemStateFiniteExact 64 F) (wc : Nat),
      LoopWork { LoopSemStateFiniteExact.setVar tmp (.word word) st with
        clock := (LoopSemStateFiniteExact.setVar tmp (.word word) st).clock + k }
        (compileHOLExact context live (if word ≠ 0 then yes else no)) output wc →
      ∃ w, LoopWork { st with clock := st.clock + k }
        (loopNestedSeqHOL [.assign tmp le,
          .ite .notEqual tmp (.imm (0 : BitVec 64))
            (compileHOLExact context live yes) (compileHOLExact context live no) live])
        (LoopSemStateFiniteExact.cutRes live output) w ∧ w ≤ 3 + loopValueWork le + wc := by
    intro k output wc child
    have hle : LoopSemStateFiniteExact.eval { st with clock := st.clock + k } le =
        some (.word word) := by
      rw [LoopSemStateFiniteExact.eval_upd_clock_eq]; simpa [wlabWlocExact] using h1v
    have assignRun : evaluate (.assign tmp le) { st with clock := st.clock + k } =
        (none, LoopSemStateFiniteExact.setVar tmp (.word word)
          { st with clock := st.clock + k }) := by
      rw [evaluate, hle]
    have assignWork := LoopWork.atom (cost := 1 + loopValueWork le) rfl assignRun
    have iteWork := LoopWork.iteBranch (live := live)
      (s := LoopSemStateFiniteExact.setVar tmp (.word word) { st with clock := st.clock + k })
      (yes := compileHOLExact context live yes) (no := compileHOLExact context live no)
      (operator := .notEqual) (register := tmp) (right := .imm (0 : BitVec 64))
      (x := word) (y := 0)
      (by simp [LoopSemStateFiniteExact.setVar, sptLookup_sptInsert])
      (by rfl) (by rw [chosen]; exact child)
    rcases hcut : LoopSemStateFiniteExact.cutRes live output with ⟨r2, s2⟩
    rw [hcut] at iteWork
    rcases r2 with _ | r2
    · have skipWork : LoopWork s2 (loopNestedSeqHOL ([] : List (HolLoopProg 64))) (none, s2) 0 :=
        LoopWork.atom (cost := 0) rfl (by rw [loopNestedSeqHOL, evaluate])
      exact ⟨1 + loopValueWork le + ((2 + wc) + 0),
        LoopWork.seqNext assignWork (LoopWork.seqNext iteWork skipWork), by omega⟩
    · exact ⟨1 + loopValueWork le + (2 + wc),
        LoopWork.seqNext assignWork (LoopWork.seqStop (second := .skip) iteWork), by omega⟩
  have h1k : ∀ k, evaluate (loopNestedSeqHOL np) { u with clock := u.clock + (ck + k) } =
      (none, { st with clock := st.clock + k }) := by
    intro k
    have := LoopSemStateFiniteExact.evaluate_add_clock_eq _ _ _ _ k h1 (by simp)
    simpa [Nat.add_assoc] using this
  have finish : ∀ (E : Nat) (k : Nat) (output : Option (LoopResultExact 64) ×
        LoopSemStateFiniteExact 64 F) (wc : Nat), E = ck + k →
      LoopWork { LoopSemStateFiniteExact.setVar tmp (.word word) st with
        clock := (LoopSemStateFiniteExact.setVar tmp (.word word) st).clock + k }
        (compileHOLExact context live (if word ≠ 0 then yes else no)) output wc →
      wc ≤ wb →
      LoopRunRel context live (evalCrepSemHOLProgExact t (if word ≠ 0 then yes else no))
        (LoopSemStateFiniteExact.cutRes live output) →
      LoopPaid context live t u (.ite condition yes no) (P.unit + P.price condition + wb) := by
    intro E k output wc hE child childBound runRel
    obtain ⟨wt, tWork, tBound⟩ := tailWork k output wc child
    obtain ⟨wTotal, totalWork, totalBound⟩ := loopWork_codes_append np _ codeCost
      { u with clock := u.clock + (ck + k) } _ _ wt codeSupported (h1k k) tWork
    rw [← hcomp] at totalWork
    have sound := LoopWork.sound totalWork
    subst hE
    refine ⟨ck + k, wTotal, ?_, by omega, ?_⟩
    · rw [sound]; exact totalWork
    · rw [sound, crepRun]; exact runRel
  rcases hbranch : evalCrepSemHOLProgExact t (if word ≠ 0 then yes else no) with ⟨res, s1⟩
  rw [hbranch] at rel'
  rcases ho : evaluate (compileHOLExact context live (if word ≠ 0 then yes else no))
      { LoopSemStateFiniteExact.setVar tmp (.word word) st with clock :=
        (LoopSemStateFiniteExact.setVar tmp (.word word) st).clock + e' } with ⟨res1, t1⟩
  rw [ho] at work' rel'
  obtain ⟨h2s, h2m, h2g, h2c, h2r, h2l⟩ := rel'
  simp only at h2s h2m h2g h2c h2r h2l
  cases res with
  | none =>
    have hr1 : res1 = none := by simpa [resultToLoop] using h2r
    subst hr1
    have lifted := LoopWork.add_clock work' 1 (by simp)
    simp only [] at lifted
    have h2l' : crepToLoopLocalsRelExact context live s1.locals t1.locals := h2l
    have hsub : LoopSemStateFiniteExact.sptSubsetLive live t1.locals := h2l'.2.2.1
    have hcut : LoopSemStateFiniteExact.cutRes live (none, { t1 with clock := t1.clock + 1 }) =
        (none, { t1 with locals := sptInter t1.locals live }) := by
      rw [LoopSemStateFiniteExact.cutRes]
      simp only
      rw [LoopSemStateFiniteExact.cutState_of_subset live { t1 with clock := t1.clock + 1 } hsub]
      simp [LoopSemStateFiniteExact.decClock]
    refine finish (ck + (e' + 1)) (e' + 1) _ wl' rfl (by simpa [Nat.add_assoc] using lifted)
      bound' ?_
    rw [hbranch, hcut]
    refine ⟨h2s, h2m, h2g, h2c, rfl, ?_⟩
    refine ⟨h2l'.1, h2l'.2.1, fun k hk => ?_, fun vn val hval => ?_⟩
    · have hk' : (sptLookup k live).isSome := hk
      show (sptLookup k (sptInter t1.locals live)).isSome
      rw [sptLookup_sptInter, if_pos hk']
      exact hsub k hk
    · obtain ⟨n, hn1, hn2, hn3⟩ := h2l'.2.2.2 vn val hval
      have hnl : (sptLookup n live).isSome := hn2
      refine ⟨n, hn1, hn2, ?_⟩
      show sptLookup n (sptInter t1.locals live) = _
      rw [sptLookup_sptInter, if_pos hnl]
      exact hn3
  | some r =>
    obtain ⟨x, hx⟩ : ∃ x, res1 = some x := by
      cases r <;> simp only [resultToLoop] at h2r <;> exact ⟨_, h2r⟩
    subst hx
    refine finish (ck + e') e' _ wl' rfl work' bound' ?_
    rw [hbranch]
    simp only [LoopSemStateFiniteExact.cutRes]
    exact ⟨h2s, h2m, h2g, h2c, h2r, h2l⟩

#print axioms ite_loop_paid
#print axioms loopWork_codes_append
#print axioms if_guard_locals
end InitECandidate.Runtime.FineCost
