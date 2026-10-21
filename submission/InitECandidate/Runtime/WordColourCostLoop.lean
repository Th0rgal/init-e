import InitECandidate.Runtime.WordColourCostBasis
import InitECandidate.Runtime.WordIselLoop

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000

/-- Loop: induction on the actual clock. Each iteration's body cost comes from
the body hypothesis at the transported cut state; the recursive iteration's
oracle is stitched into the body run with its cost preserved exactly. -/
theorem colourCost_loop {C F : Type} (price : WordLangProgHOL (BitVec 64) → Nat)
    (invariant : ColourPriceInvariant price) (names exitNames : NumSet)
    (body : WordLangProgHOL (BitVec 64)) (ihBody : ColourCostGoal C F price body) :
    ColourCostGoal C F price (.loop names body exitNames) := by
  classical
  have hrenameLn : ∀ f, applyNummapKey f (.ln : NumSet) = .ln := fun _ => rfl
  have ht := (evaluate_def_rebound (width := 64) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  suffices ∀ n (st cst : WordSemStateFiniteExact 64 C F) f live lt,
      st.clock = n →
      colouringOk f (.loop names body exitNames) live lt ∧ wordStateEqRel st cst ∧
        strongLocalsRel f (sptDomain names) st.locals cst.locals →
      ColourCostPost price f (.loop names body exitNames) live lt st cst by
    intro st cst f live lt h
    exact this st.clock st cst f live lt rfl ⟨h.1, h.2.1, by simpa only [getLive] using h.2.2⟩
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rintro st cst f live lt hn ⟨hc, hs, hl⟩
    have targetLoop : applyColour f (.loop names body exitNames) =
        .loop (applyNummapKey f names) (applyColour f body) (applyNummapKey f exitNames) := rfl
    have headPrice := invariant f (.loop names body exitNames)
    cases hcut : cutState (names, .ln) st with
    | none =>
      refine ⟨st.permute, Or.inl ?_⟩
      show (evaluate (.loop names body exitNames) st).1 = some .error
      rw [ht, hcut]
    | some entry =>
      obtain ⟨centry, hccut, hentry, hentrylocals⟩ :=
        cutStateColourTransportLive names .ln f (sptDomain (getLive body names ((names, exitNames) :: lt)))
          st cst entry
          (by simpa only [sptDomain_ln, or_false] using hc.1)
          hs (by simpa only [sptDomain_ln, or_false] using hl) hcut
      have hccut' : cutState (applyNummapKey f names, .ln) cst = some centry := by
        simpa only [applyNummapsKey, hrenameLn] using hccut
      have hbase : ∀ q, cutState (names, .ln) {st with permute := q} =
          some {entry with permute := q} := by
        intro q; rw [cutState_withPermute, hcut]; rfl
      obtain ⟨p, hp⟩ := ihBody entry centry f names ((names, exitNames) :: lt)
        ⟨hc.2.2, hentry, hentrylocals⟩
      dsimp only at hp
      rcases hb : evaluate body {entry with permute := p} with ⟨res, out⟩
      rw [hb] at hp
      dsimp only at hp
      rcases hp with herr | ⟨hres, hsout, hlout, bodyCost⟩
      · refine ⟨p, Or.inl ?_⟩
        subst herr
        simp [ht, hbase, hb, wordSemContLoop, wordSemExitLoop]
      by_cases herr : res = some .error
      · refine ⟨p, Or.inl ?_⟩
        subst herr
        simp [ht, hbase, hb, wordSemContLoop, wordSemExitLoop]
      rcases hcb : evaluate (applyColour f body) centry with ⟨cres, cout⟩
      rw [hcb] at hres hsout hlout
      dsimp only at hres hsout hlout
      subst cres
      have sourceCost : ∀ q (middle : WordSemStateFiniteExact 64 C F),
          evaluate body {entry with permute := q} = (res, middle) →
          wordExecutionCost (fun p _ => price p) (.loop names body exitNames) {st with permute := q} =
            price (.loop names body exitNames) +
              wordExecutionCost (fun p _ => price p) body {entry with permute := q} +
              (if wordSemContLoop res then
                (if middle.clock = 0 then 0
                 else wordExecutionCost (fun p _ => price p) (.loop names body exitNames) (decClock middle))
               else 0) := by
        intro q middle run
        exact loop_cost_clause _ names body exitNames _ _ (hbase q) res middle run
      have targetCost : wordExecutionCost (fun p _ => price p) (applyColour f (.loop names body exitNames)) cst =
          price (applyColour f (.loop names body exitNames)) +
            wordExecutionCost (fun p _ => price p) (applyColour f body) centry +
            (if wordSemContLoop res then
              (if cout.clock = 0 then 0
               else wordExecutionCost (fun p _ => price p) (applyColour f (.loop names body exitNames)) (decClock cout))
             else 0) := by
        rw [targetLoop]
        exact loop_cost_clause _ _ (applyColour f body) _ _ _ hccut' res cout hcb
      by_cases hcont : wordSemContLoop res = true
      · have hnames : strongLocalsRel f (sptDomain names) out.locals cout.locals := by
          cases res with
          | none => exact hlout
          | some r =>
            cases r <;> simp [wordSemContLoop] at hcont
            case «continue» k =>
              subst k
              simpa [applyColourLocals, sptOel_eq_getElem?] using hlout
        have hclock := wsrClock hsout
        by_cases hz : out.clock = 0
        · have hcz : cout.clock = 0 := hclock.trans hz
          refine ⟨p, Or.inr ⟨?_, ?_, ?_, ?_⟩⟩
          · simp only [ht, hbase, hb, targetLoop, hccut', hcb, hcont, if_true, hz, hcz]
          · simp only [ht, hbase, hb, targetLoop, hccut', hcb, hcont, if_true, hz, hcz]
            simp_all [wordStateEqRel, flushState]
          · simp only [ht, hbase, hb, targetLoop, hccut', hcb, hcont, if_true, hz, hcz]
            simp_all [applyColourLocals, flushState]
          · rw [sourceCost p out hb, targetCost]
            simp only [hcont, if_true, hz, hcz]
            omega
        · have hlt : (decClock out).clock < n := by
            have hbound := loopBodyRecursiveClockLt (names, .ln) body
              {st with permute := p} {entry with permute := p} out res (hbase p) hb hz
            simpa only [hn] using hbound
          obtain ⟨q, hq⟩ := ih (decClock out).clock hlt (decClock out) (decClock cout)
            f live lt rfl ⟨hc, wsrDecClock hsout, hnames⟩
          obtain ⟨p0, run0, cost0⟩ := word_permute_executed_cost price body
            {entry with permute := p} q (by rw [hb]; exact herr)
          rw [hb] at run0
          have run0' : evaluate body {entry with permute := p0} = (res, {out with permute := q}) := run0
          have cost0' : wordExecutionCost (fun p _ => price p) body {entry with permute := p0} =
              wordExecutionCost (fun p _ => price p) body {entry with permute := p} := cost0
          have hcz : cout.clock ≠ 0 := by rwa [hclock]
          refine ⟨p0, ?_⟩
          have hsrc : evaluate (.loop names body exitNames) {st with permute := p0} =
              evaluate (.loop names body exitNames) {decClock out with permute := q} := by
            rw [ht, hbase p0]
            simp only [run0', hcont, if_true, hz, if_false, wordSemSTOP]
            rfl
          have htgt : evaluate (applyColour f (.loop names body exitNames)) cst =
              evaluate (applyColour f (.loop names body exitNames)) (decClock cout) := by
            rw [targetLoop, ht, hccut']
            simp only [hcb, hcont, if_true, hcz, if_false, wordSemSTOP]
          dsimp only at hq ⊢
          rw [hsrc, htgt]
          rcases hq with bad | ⟨same, frame, locals, cost⟩
          · exact Or.inl bad
          · refine Or.inr ⟨same, frame, locals, ?_⟩
            rw [sourceCost p0 {out with permute := q} run0', targetCost, cost0']
            have recursive : decClock {out with permute := q} = {decClock out with permute := q} := rfl
            simp only [hcont, if_true, hcz, if_false, hz, recursive]
            omega
      · have exitCost : wordExecutionCost (fun p _ => price p) (applyColour f (.loop names body exitNames)) cst ≤
            wordExecutionCost (fun p _ => price p) (.loop names body exitNames) {st with permute := p} := by
          rw [sourceCost p out hb, targetCost]
          simp only [hcont, Bool.false_eq_true, if_false, Nat.add_zero]
          omega
        cases res with
        | none => simp [wordSemContLoop] at hcont
        | some r =>
          cases r with
          | «break» k =>
            cases k with
            | zero =>
              cases hexit : cutState (exitNames, .ln) out with
              | none =>
                refine ⟨p, Or.inl ?_⟩
                simp only [ht, hbase, hb, wordSemContLoop, Bool.false_eq_true, if_false, hexit]
              | some final =>
                obtain ⟨cfinal, hcexit, hsfinal, hdom, hlocal, _⟩ :=
                  cutStateColourTransport exitNames .ln f out cout final
                    (by simpa only [sptDomain_ln, or_false] using hc.2.1)
                    hsout
                    (by simpa [applyColourLocals, sptOel_eq_getElem?, sptDomain_ln] using hlout)
                    hexit
                have hcexit' : cutState (applyNummapKey f exitNames, .ln) cout = some cfinal := by
                  simpa only [applyNummapsKey, hrenameLn] using hcexit
                refine ⟨p, Or.inr ⟨?_, ?_, ?_, exitCost⟩⟩
                · simp only [ht, hbase, hb, targetLoop, hccut', hcb, wordSemContLoop,
                    Bool.false_eq_true, if_false, hexit, hcexit']
                · simp only [ht, hbase, hb, targetLoop, hccut', hcb, wordSemContLoop,
                    Bool.false_eq_true, if_false, hexit, hcexit']
                  exact hsfinal
                · simp only [ht, hbase, hb, targetLoop, hccut', hcb, wordSemContLoop,
                    Bool.false_eq_true, if_false, hexit, hcexit']
                  exact strongLocalsRelExtendAux f _ (sptDomain live) _ _
                    ⟨fun key hk => by rwa [hdom] at hk, hlocal⟩
            | succ k =>
              refine ⟨p, Or.inr ⟨?_, ?_, ?_, exitCost⟩⟩
              all_goals
                simp only [ht, hbase, hb, targetLoop, hccut', hcb, wordSemContLoop,
                  Bool.false_eq_true, if_false, wordSemExitLoop, Nat.add_sub_cancel]
              · exact hsout
              · simpa [applyColourLocals, sptOel_eq_getElem?] using hlout
          | «continue» k =>
            have hk : k ≠ 0 := by simpa [wordSemContLoop] using hcont
            cases k with
            | zero => contradiction
            | succ k =>
              refine ⟨p, Or.inr ⟨?_, ?_, ?_, exitCost⟩⟩
              all_goals
                simp only [ht, hbase, hb, targetLoop, hccut', hcb, hcont, Bool.false_eq_true,
                  if_false, wordSemExitLoop, Nat.add_sub_cancel]
              · exact hsout
              · simpa [applyColourLocals, sptOel_eq_getElem?] using hlout
          | error => exact (herr rfl).elim
          | result a b | exception a b | timeOut | notEnoughSpace | finalFfi =>
            refine ⟨p, Or.inr ⟨?_, ?_, ?_, exitCost⟩⟩
            all_goals
              simp only [ht, hbase, hb, targetLoop, hccut', hcb, wordSemContLoop,
                Bool.false_eq_true, if_false, wordSemExitLoop]
            · exact hsout
            · simpa [applyColourLocals] using hlout

#print axioms colourCost_loop
end InitECandidate.Runtime.FineCost
