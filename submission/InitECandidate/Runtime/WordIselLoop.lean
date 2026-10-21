import InitECandidate.Runtime.WordIselCompound
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact

/-! Loop case of the instruction-selection transfer: by induction on the clock,
each iteration's body transfers from the cut state (whose locals are identical
on both sides), and the next iteration runs at the decremented clock. -/

theorem loop_cost_clause {C F : Type} (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (names : WordLangNumSetHOL) (body : WordLangProgHOL (BitVec 64)) (exitNames : WordLangNumSetHOL)
    (s cs : WordSemStateFiniteExact 64 C F) (hcs : cutState (names, .ln) s = some cs)
    (r1 : Option (WordSemResult 64)) (s1 : WordSemStateFiniteExact 64 C F) (hb : evaluate body cs = (r1, s1)) :
    wordExecutionCost price (.loop names body exitNames) s =
      price (.loop names body exitNames) s + wordExecutionCost price body cs +
        (if wordSemContLoop r1 then
          (if s1.clock = 0 then 0 else wordExecutionCost price (.loop names body exitNames) (decClock s1))
         else 0) := by
  rw [wordExecutionCost]
  split
  · rename_i h; rw [hcs] at h; cases h
  · rename_i cs' h
    rw [hcs] at h; cases h
    have hf : fixClock cs (r1, s1) = (r1, s1) := by rw [← hb]; exact fix_clock_evaluate cs body
    simp only [hb, hf, wordSemSTOP]
    split <;> simp_all

theorem loop_cost_cut_none {C F : Type} (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (names : WordLangNumSetHOL) (body : WordLangProgHOL (BitVec 64)) (exitNames : WordLangNumSetHOL)
    (s : WordSemStateFiniteExact 64 C F) (hcs : cutState (names, .ln) s = none) :
    wordExecutionCost price (.loop names body exitNames) s = price (.loop names body exitNames) s := by
  rw [wordExecutionCost]
  split
  · rfl
  · rename_i cs' h; rw [hcs] at h; cases h

theorem cutState_rel {C F : Type} {c : Compiler.Encoders.Asm.AsmConfigExact 64} {temp : Nat}
    {s t : WordSemStateFiniteExact 64 C F} (rel : IselRel c temp s t) (names : WordLangNumSetHOL)
    (hn : everyNameHOL (fun x => decide (x < temp)) (names, .ln) = true) (env : Spt (WordLocW 64))
    (hc : wordSemCutEnv (names, .ln) s.locals = some env) :
    cutState (names, .ln) s = some { s with locals := env } ∧
      cutState (names, .ln) t = some { t with locals := env } ∧
      IselRel c temp { s with locals := env } { t with locals := env } := by
  have hc' := locals_rel_cut_env temp s.locals t.locals (names, .ln) env ⟨rel.1, hn, hc⟩
  refine ⟨by unfold cutState; rw [hc], by unfold cutState; rw [hc'], fun _ _ => rfl, rel.2.1, ?_⟩
  conv_lhs => rw [rel.2.2]

theorem isel_loop_aux {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) (td ck temp : Nat)
    (names : WordLangNumSetHOL) (body : WordLangProgHOL (BitVec 64)) (exitNames : WordLangNumSetHOL)
    (hb : IselGoal (C := C) (F := F) c td ck temp body) (ih : IselCalleeIH (C := C) (F := F) c td ck)
    (hn : everyNameHOL (fun x => decide (x < temp)) (names, .ln) = true)
    (hbv : everyVarHOL (fun x => decide (x < temp)) body = true)
    (hx : everyNameHOL (fun x => decide (x < temp)) (exitNames, .ln) = true) :
    ∀ (n : Nat) (s t : WordSemStateFiniteExact 64 C F), s.clock = n → LexLe s.termdep s.clock td ck →
      IselRel c temp s t → ∀ (res : Option (WordSemResult 64)) (rst : WordSemStateFiniteExact 64 C F),
      evaluate (.loop names body exitNames) s = (res, rst) → res ≠ some .error →
      ∃ rstT, evaluate (.loop names (WordInst.instSelectExecutable c temp body) exitNames) t = (res, rstT) ∧
        IselPost c temp res rst rstT ∧
        wordExecutionCost wordOptimizerLocalPrice (.loop names (WordInst.instSelectExecutable c temp body) exitNames) t ≤
          wordExecutionCost (preIselPrice c) (.loop names body exitNames) s := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n IH =>
  intro s t hsn le rel res rst run ok
  have ht := (evaluate_def_rebound (width := 64) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [ht] at run
  rcases hc : wordSemCutEnv (names, .ln) s.locals with _ | env
  · have hcs : cutState (names, .ln) s = none := by unfold cutState; rw [hc]
    rw [hcs] at run; simp only [Prod.mk.injEq] at run; exact absurd run.1.symm ok
  obtain ⟨hcs, hct, crel⟩ := cutState_rel rel names hn env hc
  rw [hcs] at run
  simp only at run
  rcases hbr : evaluate body { s with locals := env } with ⟨r1, s1⟩
  rw [hbr] at run
  have hr1 : r1 ≠ some .error := by
    rintro rfl
    simp [wordSemContLoop, wordSemExitLoop] at run
    exact ok run.1.symm
  obtain ⟨t1, ht1, post1, cost1⟩ := hb ih { s with locals := env } { t with locals := env } r1 s1 le hbv crel hbr hr1
  have t1Eq := post1.2.2
  have tClock : t1.clock = s1.clock := by rw [t1Eq]
  have tgtRun := ht t names exitNames (WordInst.instSelectExecutable c temp body)
  rw [hct] at tgtRun
  simp only at tgtRun
  rw [ht1] at tgtRun
  simp only at tgtRun
  have costS := loop_cost_clause (preIselPrice c) names body exitNames s _ hcs r1 s1 hbr
  have costT := loop_cost_clause wordOptimizerLocalPrice names (WordInst.instSelectExecutable c temp body)
    exitNames t _ hct r1 t1 ht1
  have prices : wordOptimizerLocalPrice (.loop names (WordInst.instSelectExecutable c temp body) exitNames) t ≤
      preIselPrice c (.loop names body exitNames) s := by
    simp [preIselPrice, wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
      WordToStack.refinedWordStackLeafBudget]
  by_cases hcont : wordSemContLoop r1 = true
  · simp only [hcont, if_true] at run tgtRun costS costT
    have rel1 : IselRel c temp s1 t1 := by
      refine ⟨?_, post1.2.1, post1.2.2⟩
      have p1 := post1.1
      rcases r1 with _ | (_ | _ | _ | _ | _ | _ | _ | _) <;> simp [wordSemContLoop] at hcont <;> exact p1
    by_cases hz : s1.clock = 0
    · simp only [hz, if_true, Prod.mk.injEq] at run
      obtain ⟨rfl, rfl⟩ := run
      rw [tClock] at tgtRun costT
      simp only [hz, if_true] at tgtRun costT costS
      refine ⟨flushState true t1, tgtRun, ⟨?_, ?_, ?_⟩, by omega⟩
      · show WordSemStateFiniteExact.LrPost temp (some .timeOut) (flushState true s1).locals (flushState true t1).locals
        simp [WordSemStateFiniteExact.LrPost, flushState]
      · simpa [flushState] using post1.2.1
      · simp only [flushState]; conv_lhs => rw [t1Eq]
    · simp only [hz, if_false, wordSemSTOP] at run
      rw [tClock] at tgtRun costT
      simp only [hz, if_false, wordSemSTOP] at tgtRun costT costS
      have hc1 := evaluate_clock body _ r1 s1 hbr
      have hlt : (decClock s1).clock < n := by simp only [decClock] at hc1 ⊢; omega
      have leD : LexLe (decClock s1).termdep (decClock s1).clock td ck := by
        have := lexLe_of_run hbr le
        simp only [decClock]; rcases this with h | ⟨h1, h2⟩
        · exact Or.inl h
        · exact Or.inr ⟨h1, by omega⟩
      have relD : IselRel c temp (decClock s1) (decClock t1) := by
        refine ⟨rel1.1, rel1.2.1, ?_⟩
        simp only [decClock]; rw [tClock]; conv_lhs => rw [t1Eq]
      obtain ⟨rT, hrT, postT, costD⟩ := IH _ hlt (decClock s1) (decClock t1) rfl leD relD res rst run ok
      refine ⟨rT, tgtRun.trans hrT, postT, by omega⟩
  · simp only [hcont, Bool.false_eq_true, if_false] at run tgtRun costS costT
    rcases r1 with _ | (_ | _ | (_ | k) | (_ | k) | _ | _ | _ | _)
    all_goals try (simp [wordSemContLoop] at hcont; done)
    all_goals simp only at run tgtRun
    all_goals try (simp only [Prod.mk.injEq] at run
                   obtain ⟨rfl, rfl⟩ := run
                   first
                     | exact absurd rfl hr1
                     | exact ⟨t1, tgtRun, post1, by omega⟩)
    -- break 0: the exit cut
    rcases hce : wordSemCutEnv (exitNames, .ln) s1.locals with _ | env2
    · have : cutState (exitNames, .ln) s1 = none := by unfold cutState; rw [hce]
      rw [this] at run; simp only [Prod.mk.injEq] at run; exact absurd run.1.symm ok
    have rel1 : IselRel c temp s1 t1 := ⟨post1.1, post1.2.1, post1.2.2⟩
    obtain ⟨hcs2, hct2, crel2⟩ := cutState_rel rel1 exitNames hx env2 hce
    rw [hcs2] at run; simp only [Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    rw [hct2] at tgtRun
    exact ⟨_, tgtRun, crel2, by omega⟩

theorem isel_loop_step {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) (td ck temp : Nat)
    (names : WordLangNumSetHOL) (body : WordLangProgHOL (BitVec 64)) (exitNames : WordLangNumSetHOL)
    (hb : IselGoal (C := C) (F := F) c td ck temp body) :
    IselGoal (C := C) (F := F) c td ck temp (.loop names body exitNames) := by
  intro ih s t res rst le vars rel run ok
  simp only [everyVarHOL, Bool.and_eq_true] at vars
  have sel : WordInst.instSelectExecutable c temp (.loop names body exitNames) =
      .loop names (WordInst.instSelectExecutable c temp body) exitNames := by
    simp [WordInst.instSelectExecutable]
  rw [sel]
  exact isel_loop_aux c td ck temp names body exitNames hb ih
    (by simp [everyNameHOL, vars.1.1]) vars.1.2 (by simp [everyNameHOL, vars.2]) s.clock s t rfl le rel res rst run ok

#print axioms isel_loop_step
end InitECandidate.Runtime.FineCost
