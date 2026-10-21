import InitECandidate.Runtime.WordColourIndexedControl
import InitECandidate.Runtime.WordColourCostLoop

namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordAlloc
open Flapjack.WordSemStateFiniteExact
set_option maxHeartbeats 6000000

theorem cutState_withCode {C F : Type} (names : WordLangCutsetsHOL) (s : WordSemStateFiniteExact 64 C F)
    (code : Spt (Nat × WordLangProgHOL (BitVec 64))) :
    cutState names {s with code := code} = (cutState names s).map (fun t => {t with code := code}) := by
  unfold cutState
  cases wordSemCutEnv names s.locals <;> rfl

theorem cutState_code {C F : Type} (names : WordLangCutsetsHOL) (s t : WordSemStateFiniteExact 64 C F)
    (cut : cutState names s = some t) : t.code = s.code := by
  unfold cutState at cut
  cases h : wordSemCutEnv names s.locals with
  | none => rw [h] at cut; cases cut
  | some env => rw [h] at cut; cases cut; rfl

/-- `cutStateColourTransport` with the target over its own function table. -/
theorem cutStateColourTransportCode {C F : Type} (n1 n2 : NumSet) (f : Nat → Nat)
    (st cst rst : WordSemStateFiniteExact 64 C F)
    (hinj : ∀ a b, (sptDomain n1 a ∨ sptDomain n2 a) →
      (sptDomain n1 b ∨ sptDomain n2 b) → f a = f b → a = b)
    (hs : wordStateEqRel st {cst with code := st.code})
    (hl : strongLocalsRel f (fun key => sptDomain n1 key ∨ sptDomain n2 key) st.locals cst.locals)
    (hc : cutState (n1, n2) st = some rst) :
    ∃ rcst, cutState (applyNummapsKey f (n1, n2)) cst = some rcst ∧
      wordStateEqRel rst {rcst with code := rst.code} ∧
      sptDomain rst.locals = (fun key => sptDomain n1 key ∨ sptDomain n2 key) ∧
      strongLocalsRel f (fun key => sptDomain n1 key ∨ sptDomain n2 key) rst.locals rcst.locals ∧
      sptDomain rcst.locals = (fun key => ∃ source, sptDomain rst.locals source ∧ f source = key) := by
  obtain ⟨down, hdown, heq, hd, hr, hdd⟩ :=
    cutStateColourTransport n1 n2 f st {cst with code := st.code} rst hinj hs hl hc
  have restore : ({({cst with code := st.code} : WordSemStateFiniteExact 64 C F) with code := cst.code}) = cst := rfl
  have targetCut : cutState (applyNummapsKey f (n1, n2)) cst = some {down with code := cst.code} := by
    rw [← restore, cutState_withCode, hdown]
    rfl
  have downCode : down.code = st.code := cutState_code _ ({cst with code := st.code} : WordSemStateFiniteExact 64 C F) _ hdown
  have rstCode : rst.code = st.code := cutState_code _ _ _ hc
  refine ⟨{down with code := cst.code}, targetCut, ?_, hd, hr, hdd⟩
  have shape : ({({down with code := cst.code} : WordSemStateFiniteExact 64 C F) with code := rst.code}) = down := by
    rw [rstCode, ← downCode]
  rw [shape]
  exact heq

theorem cutStateColourTransportLiveCode {C F : Type} (n1 n2 : NumSet) (f : Nat → Nat) (live : Nat → Prop)
    (st cst rst : WordSemStateFiniteExact 64 C F)
    (hinj : ∀ a b, (sptDomain n1 a ∨ sptDomain n2 a) →
      (sptDomain n1 b ∨ sptDomain n2 b) → f a = f b → a = b)
    (hs : wordStateEqRel st {cst with code := st.code})
    (hl : strongLocalsRel f (fun key => sptDomain n1 key ∨ sptDomain n2 key) st.locals cst.locals)
    (hc : cutState (n1, n2) st = some rst) :
    ∃ rcst, cutState (applyNummapsKey f (n1, n2)) cst = some rcst ∧
      wordStateEqRel rst {rcst with code := rst.code} ∧ strongLocalsRel f live rst.locals rcst.locals := by
  obtain ⟨rcst, ht, heq, hd, hr, hdd⟩ := cutStateColourTransportCode n1 n2 f st cst rst hinj hs hl hc
  refine ⟨rcst, ht, heq, strongLocalsRelExtendAux f _ live _ _ ⟨?_, hr⟩⟩
  intro key hk
  rwa [hd] at hk

theorem colourIndexed_loop {C F : Type} (TP : WordLangProgHOL (BitVec 64) → Nat)
    (SP : Nat → WordLangProgHOL (BitVec 64) → Nat)
    (source target : Spt (Nat × WordLangProgHOL (BitVec 64))) (col : Nat → Nat → Nat)
    (function : Nat) (f : Nat → Nat)
    (sourceFree : WordProps.noInstallCode source) (targetFree : WordProps.noInstallCode target)
    (leafPrice : ∀ p, TP (applyColour f p) ≤ SP function p)
    (permuteCost : IndexedPermuteCost C F SP) (names exitNames : NumSet)
    (body : WordLangProgHOL (BitVec 64))
    (ihBody : ColourIndexedGoal C F TP SP source target col function f body) :
    ColourIndexedGoal C F TP SP source target col function f (.loop names body exitNames) := by
  classical
  have hrenameLn : ∀ f, applyNummapKey f (.ln : NumSet) = .ln := fun _ => rfl
  have ht := (evaluate_def_rebound (width := 64) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have bodyFreeOf : noInstallSubprogsHOL (.loop names body exitNames : WordLangProgHOL (BitVec 64)) = true →
      noInstallSubprogsHOL body = true := by
    intro free
    simpa only [noInstallSubprogsHOL, notCreatedSubprogsWithMemOp] using free
  suffices ∀ n (st cst : WordSemStateFiniteExact 64 C F) live lt,
      st.clock = n → ColourCalleeIH C F TP SP source target col st.termdep st.clock → noInstallSubprogsHOL (.loop names body exitNames : WordLangProgHOL (BitVec 64)) = true →
      st.code = source → cst.code = target →
      colouringOk f (.loop names body exitNames) live lt ∧ wordStateEqRel st {cst with code := st.code} ∧
        strongLocalsRel f (sptDomain names) st.locals cst.locals →
      ColourIndexedPost TP SP function f (.loop names body exitNames) live lt st cst by
    intro st cst live lt calleeIH free sourceCode targetCode h
    exact this st.clock st cst live lt rfl calleeIH free sourceCode targetCode
      ⟨h.1, h.2.1, by simpa only [getLive] using h.2.2⟩
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rintro st cst live lt hn calleeIH free sourceCode targetCode ⟨hc, hs, hl⟩
    have bodyFree := bodyFreeOf free
    have targetLoop : applyColour f (.loop names body exitNames) =
        .loop (applyNummapKey f names) (applyColour f body) (applyNummapKey f exitNames) := rfl
    have headPrice := leafPrice (.loop names body exitNames)
    cases hcut : cutState (names, .ln) st with
    | none =>
      refine ⟨st.permute, Or.inl ?_⟩
      show (evaluate (.loop names body exitNames) st).1 = some .error
      rw [ht, hcut]
    | some entry =>
      obtain ⟨centry, hccut, hentry, hentrylocals⟩ :=
        cutStateColourTransportLiveCode names .ln f (sptDomain (getLive body names ((names, exitNames) :: lt)))
          st cst entry
          (by simpa only [sptDomain_ln, or_false] using hc.1)
          hs (by simpa only [sptDomain_ln, or_false] using hl) hcut
      have hccut' : cutState (applyNummapKey f names, .ln) cst = some centry := by
        simpa only [applyNummapsKey, hrenameLn] using hccut
      have hbase : ∀ q, cutState (names, .ln) {st with permute := q} =
          some {entry with permute := q} := by
        intro q; rw [cutState_withPermute, hcut]; rfl
      have entryCode : entry.code = source := (cutState_code _ _ _ hcut).trans sourceCode
      have centryCode : centry.code = target := (cutState_code _ _ _ hccut).trans targetCode
      have entryClocks := cutState_clock_termdep (names, .ln) st entry hcut
      obtain ⟨p, hp⟩ := ihBody entry centry names ((names, exitNames) :: lt)
        (calleeIH.mono (by right; exact ⟨entryClocks.2, entryClocks.1.le⟩)) bodyFree entryCode centryCode
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
          wordFunctionExecutionCost (fun l p _ => SP l p) function (.loop names body exitNames) {st with permute := q} =
            SP function (.loop names body exitNames) +
              wordFunctionExecutionCost (fun l p _ => SP l p) function body {entry with permute := q} +
              (if wordSemContLoop res then
                (if middle.clock = 0 then 0
                 else wordFunctionExecutionCost (fun l p _ => SP l p) function (.loop names body exitNames) (decClock middle))
               else 0) := by
        intro q middle run
        exact function_loop_cost_clause _ function names body exitNames _ _ (hbase q) res middle run
      have targetCost : wordExecutionCost (fun p _ => TP p) (applyColour f (.loop names body exitNames)) cst =
          TP (applyColour f (.loop names body exitNames)) +
            wordExecutionCost (fun p _ => TP p) (applyColour f body) centry +
            (if wordSemContLoop res then
              (if cout.clock = 0 then 0
               else wordExecutionCost (fun p _ => TP p) (applyColour f (.loop names body exitNames)) (decClock cout))
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
          have outCode : out.code = source := by
            have h := run_code body {entry with permute := p} bodyFree
              (by rw [show ({entry with permute := p} : WordSemStateFiniteExact 64 C F).code = entry.code from rfl,
                entryCode]; exact sourceFree)
            rw [hb] at h
            exact h.trans entryCode
          have coutCode : cout.code = target := by
            have h := run_code (applyColour f body) centry (noInstall_applyColour f body bodyFree)
              (by rw [centryCode]; exact targetFree)
            rw [hcb] at h
            exact h.trans centryCode
          have outClocks := evaluate_clock body {entry with permute := p} res out hb
          obtain ⟨q, hq⟩ := ih (decClock out).clock hlt (decClock out) (decClock cout)
            live lt rfl (calleeIH.mono (by
              right
              simp only [decClock]
              exact ⟨outClocks.2.trans entryClocks.2, by have := entryClocks.1; simp only at outClocks; omega⟩))
            free outCode coutCode
            ⟨hc, by simpa [decClock, wordStateEqRel] using wsrDecClock hsout, hnames⟩
          obtain ⟨p0, run0, cost0⟩ := permuteCost function body
            {entry with permute := p} q (by rw [hb]; exact herr)
          rw [hb] at run0
          have run0' : evaluate body {entry with permute := p0} = (res, {out with permute := q}) := run0
          have cost0' : wordFunctionExecutionCost (fun l p _ => SP l p) function body {entry with permute := p0} =
              wordFunctionExecutionCost (fun l p _ => SP l p) function body {entry with permute := p} := cost0
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
      · have exitCost : wordExecutionCost (fun p _ => TP p) (applyColour f (.loop names body exitNames)) cst ≤
            wordFunctionExecutionCost (fun l p _ => SP l p) function (.loop names body exitNames) {st with permute := p} := by
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
                  cutStateColourTransportCode exitNames .ln f out cout final
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

#print axioms cutStateColourTransportCode
#print axioms colourIndexed_loop
end InitECandidate.Runtime.FineCost
