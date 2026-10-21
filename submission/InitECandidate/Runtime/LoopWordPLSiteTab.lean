import InitECandidate.Runtime.LoopWordPLRelabel
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

theorem memStore_code {F : Type} {a : BitVec 64} {w : WordLocW 64} {s t : LoopSemStateFiniteExact 64 F}
    (h : memStore a w s = some t) : t.code = s.code := by
  unfold memStore at h; split at h <;> cases h; rfl

theorem loopArith_code {F : Type} {op : LoopArith} {s t : LoopSemStateFiniteExact 64 F}
    (h : s.loopArith op = some t) : t.code = s.code := by
  cases op <;> simp only [LoopSemStateFiniteExact.loopArith] at h <;> (repeat' split at h)
  all_goals cases h
  all_goals rfl

theorem shMemOp_code {F : Type} (op : WordMemOp) (n : Nat) (a : BitVec 64) (s : LoopSemStateFiniteExact 64 F) :
    (shMemOp op n a s).2.code = s.code := by
  unfold shMemOp
  repeat' split
  all_goals simp only [shMemLoad, shMemStore]
  all_goals (repeat' split)
  all_goals simp_all [setVar, LoopSemStateFiniteExact.callEnv]

theorem cutState_code {F : Type} {live : NumSet} {s t : LoopSemStateFiniteExact 64 F}
    (h : cutState live s = some t) : t.code = s.code := by
  unfold cutState at h
  split at h <;> cases h; rfl

theorem leaf_code {F : Type} (p : HolLoopProg 64) (hp : (loopWorkLeafCost p).isSome = true)
    (s : LoopSemStateFiniteExact 64 F) : (evaluate p s).2.code = s.code := by
  cases p <;> simp [loopWorkLeafCost] at hp
  all_goals rw [evaluate.eq_def]
  all_goals try simp only
  all_goals try (repeat' split)
  all_goals first
    | rfl
    | exact memStore_code ‹_›
    | exact loopArith_code ‹_›
    | exact cutState_code ‹cutState _ _ = some _›
    | exact shMemOp_code _ _ _ _
    | simp_all [setVar, setVars, decClock, setGlobals, LoopSemStateFiniteExact.callEnv]
  all_goals exact cutState_code ‹cutState _ _ = some _›

theorem cutRes_code {F : Type} (live : NumSet) (o : Option (LoopResultExact 64) × LoopSemStateFiniteExact 64 F) :
    (cutRes live o).2.code = o.2.code := by
  rcases o with ⟨r, st⟩
  unfold cutRes
  repeat' split
  all_goals first
    | rfl
    | exact cutState_code ‹_›
    | (simp only [decClock]; exact cutState_code ‹_›)
    | simp_all [cutState_code]

theorem callShort_code {F : Type} {s : LoopSemStateFiniteExact 64 F} {returns target arguments handler output}
    (short : loopCallShort s returns target arguments handler)
    (run : evaluate (.call returns target arguments handler) s = output) : output.2.code = s.code := by
  rw [evaluate] at run
  rcases short with h | ⟨values, hv, h | ⟨env, prog, hf, short⟩⟩
  · simp only [h] at run; subst run; rfl
  · simp only [hv, h] at run; subst run; rfl
  · simp only [hv, hf] at run
    rcases short with ⟨rfl, hh | hz⟩ | ⟨names, live, rfl, hnd | ⟨result, cut, hcr⟩⟩
    · simp only [hh, ↓reduceIte] at run; subst run; rfl
    · cases handler <;> simp_all <;> (subst run; rfl)
    · simp only [hnd, not_false_eq_true, ↓reduceIte] at run; subst run; rfl
    · by_cases hnd : names.Nodup
      · simp only [hnd, not_true_eq_false, ↓reduceIte] at run
        split at run
        · rename_i h; rw [hcr] at h; cases h
        · rw [hcr] at run
          subst run
          have := cutRes_code live (none, s)
          rw [hcr] at this
          exact this
      · simp only [hnd, not_false_eq_true, ↓reduceIte] at run; subst run; rfl

theorem tailExit_code {F : Type} (r : Option (LoopResultExact 64)) (post : LoopSemStateFiniteExact 64 F) :
    (loopTailExit r post).2.code = post.code := by
  unfold loopTailExit; split <;> rfl

theorem setVars_code {F : Type} (names : List Nat) (vs : List (WordLocW 64)) (st : LoopSemStateFiniteExact 64 F) :
    (LoopSemStateFiniteExact.setVars names vs st).code = st.code := by
  simp [LoopSemStateFiniteExact.setVars]

theorem retExit_code {F : Type} (r : Option (LoopResultExact 64)) (post caller : LoopSemStateFiniteExact 64 F)
    (names : List Nat) : (loopRetExit r post caller names).2.code = post.code := by
  unfold loopRetExit; repeat' split
  all_goals simp [setVars_code]

theorem cut_entry_code {F : Type} {live : NumSet} {s entry : LoopSemStateFiniteExact 64 F} {r}
    (cut : cutRes live (none, s) = (r, entry)) : entry.code = s.code := by
  have := cutRes_code live (none, s); rw [cut] at this; exact this

/-- Executed Loop runs never change the code table. -/
theorem LoopWorkPL.code {F : Type} {lp : LoopPriceL}
    (hdom : ∀ p c, lp.base.leaf p = some c → (loopWorkLeafCost p).isSome = true)
    {l : Nat × Nat} {s : LoopSemStateFiniteExact 64 F} {p : HolLoopProg 64} {output} {w : Nat}
    (work : LoopWorkPL lp l s p output w) : output.2.code = s.code := by
  induction work with
  | atom leaf run => rw [← run]; exact leaf_code _ (hdom _ _ leaf) _
  | mark _ ih => exact ih
  | seqNext _ _ ih1 ih2 => exact ih2.trans ih1
  | seqStop _ ih => exact ih
  | iteBranch _ _ _ ih => rw [cutRes_code]; exact ih
  | iteInvalid => rfl
  | loopNext cut _ _ _ ih1 ih2 => exact ih2.trans (ih1.trans (by exact cut_entry_code cut))
  | loopBreak cut _ ih => rw [cutRes_code]; exact ih.trans (by exact cut_entry_code cut)
  | loopExit cut _ _ ih => exact ih.trans (by exact cut_entry_code cut)
  | loopCut stopped => exact cut_entry_code stopped
  | callShort short run => exact callShort_code short run
  | callTail _ _ _ _ _ ih => rw [tailExit_code]; exact ih
  | callRet _ _ _ cut _ _ ih => have he := cut_entry_code cut; rw [retExit_code]; exact ih.trans he
  | callRetCont _ _ _ cut _ _ _ ih1 ih2 =>
    have he := cut_entry_code cut
    rw [cutRes_code]; exact ih2.trans ((setVars_code _ _ _).trans (ih1.trans he))
  | callHandle _ _ _ cut _ _ ih1 ih2 =>
    have he := cut_entry_code cut
    rw [cutRes_code]; exact ih2.trans (ih1.trans he)

#print axioms LoopWorkPL.code

/-- Static label walk: every returning call of `p`, at the label `compHOL`
gives it, has site charge `A ≤ B`. -/
def SiteLe (A B : Nat × Nat → Option Nat → Nat) : Nat × Nat → HolLoopProg 64 → Prop
  | l, .mark p => SiteLe A B l p
  | l, .seq a b => SiteLe A B l a ∧ SiteLe A B (labAfter a l) b
  | l, .ite _ _ _ y n _ => SiteLe A B l y ∧ SiteLe A B (labAfter y l) n
  | l, .loop _ b _ => SiteLe A B l b
  | l, .call (some _) t _ h =>
      A l t ≤ B l t ∧
        (match h with
         | some (_, hp, cont, _) => SiteLe A B (l.1, l.2 + 1) hp ∧ SiteLe A B (labAfter hp (l.1, l.2 + 1)) cont
         | none => True)
  | _, _ => True

/-- Every callee body in the code table passes the walk at its entry label. -/
def CodeSiteLe {F : Type} (A B : Nat × Nat → Option Nat → Nat) (s : LoopSemStateFiniteExact 64 F) : Prop :=
  ∀ target values env prog, LoopSemStateFiniteExact.findCode target values s.code = some (env, prog) →
    SiteLe A B (calleeName target values, 2) prog

theorem codeSiteLe_of_code {F : Type} {A B : Nat × Nat → Option Nat → Nat} {s t : LoopSemStateFiniteExact 64 F}
    (h : CodeSiteLe A B s) (code : t.code = s.code) : CodeSiteLe A B t := by
  intro target values env prog found; rw [code] at found; exact h _ _ _ _ found

/-- Raising certified site charges: a labelled run under `lp` has a matching
run under `lp` with site `B`, of no smaller work. -/
theorem LoopWorkPL.site_mono {F : Type} {lp : LoopPriceL} (B : Nat × Nat → Option Nat → Nat)
    (hdom : ∀ p c, lp.base.leaf p = some c → (loopWorkLeafCost p).isSome = true)
    {l : Nat × Nat} {s : LoopSemStateFiniteExact 64 F} {p : HolLoopProg 64} {output} {w : Nat}
    (work : LoopWorkPL lp l s p output w) :
    SiteLe lp.site B l p → CodeSiteLe lp.site B s →
      ∃ w', LoopWorkPL { lp with site := B } l s p output w' ∧ w ≤ w' := by
  induction work with
  | atom leaf run => intro _ _; exact ⟨_, .atom leaf run, Nat.le_refl _⟩
  | mark _ ih =>
    intro hs hc; obtain ⟨w', a, h⟩ := ih hs hc; exact ⟨w', .mark a, h⟩
  | seqNext one _ ih1 ih2 =>
    intro hs hc
    obtain ⟨a', a, h1⟩ := ih1 hs.1 hc
    obtain ⟨b', b, h2⟩ := ih2 hs.2 (codeSiteLe_of_code hc (one.code hdom))
    exact ⟨_, .seqNext a b, by omega⟩
  | seqStop _ ih =>
    intro hs hc; obtain ⟨w', a, h⟩ := ih hs.1 hc; exact ⟨w', .seqStop a, h⟩
  | @iteBranch l s operator register right yes no live x y output w lhs rhs _ ih =>
    intro hs hc
    have hb : SiteLe lp.site B (if Compiler.Encoders.Asm.wordCmpHOL operator x y then l else labAfter yes l)
        (if Compiler.Encoders.Asm.wordCmpHOL operator x y then yes else no) := by
      split
      · exact hs.1
      · exact hs.2
    obtain ⟨w', a, h⟩ := ih hb hc
    exact ⟨_, .iteBranch lhs rhs a, by simp only; omega⟩
  | iteInvalid invalid => intro _ _; exact ⟨1, .iteInvalid invalid, Nat.le_refl _⟩
  | loopNext cut one again _ ih1 ih2 =>
    intro hs hc
    have hce := codeSiteLe_of_code hc (cut_entry_code cut)
    obtain ⟨a', a, h1⟩ := ih1 hs hce
    obtain ⟨b', b, h2⟩ := ih2 hs (codeSiteLe_of_code hce (one.code hdom))
    exact ⟨_, .loopNext cut a again b, by simp only; omega⟩
  | loopBreak cut _ ih =>
    intro hs hc
    obtain ⟨a', a, h⟩ := ih hs (codeSiteLe_of_code hc (cut_entry_code cut))
    exact ⟨_, .loopBreak cut a, by simp only; omega⟩
  | loopExit cut _ stop ih =>
    intro hs hc
    obtain ⟨a', a, h⟩ := ih hs (codeSiteLe_of_code hc (cut_entry_code cut))
    exact ⟨_, .loopExit cut a stop, by simp only; omega⟩
  | loopCut stopped => intro _ _; exact ⟨_, .loopCut stopped, Nat.le_refl _⟩
  | @callShort l s returns target arguments handler output short run =>
    intro hs _
    refine ⟨_, .callShort short run, ?_⟩
    rcases returns with _ | ⟨names, live⟩
    · simp only; omega
    · have := (by unfold SiteLe at hs; exact hs.1 : lp.site l target ≤ B l target); simp only; omega
  | @callTail l s target arguments handler values env prog result post wb args find noHandler clock _ ih =>
    intro _ hc
    obtain ⟨a', a, h⟩ := ih (hc _ _ _ _ find) (codeSiteLe_of_code hc rfl)
    exact ⟨_, .callTail args find noHandler clock a, by simp only; omega⟩
  | @callRet l s names live target arguments handler values env prog entry result post wb args find nodup cut _
      plain ih =>
    intro hs hc
    have hce := codeSiteLe_of_code hc (cut_entry_code cut)
    obtain ⟨a', a, h⟩ := ih (hc _ _ _ _ find) (codeSiteLe_of_code hce rfl)
    have := (by unfold SiteLe at hs; exact hs.1 : lp.site l target ≤ B l target)
    exact ⟨_, .callRet args find nodup cut a plain, by simp only; omega⟩
  | @callRetCont l s names live target arguments exceptionName handlerProgram continuation liveOut values env prog
      entry returned post wb output wc args find nodup cut body lengths _ ih1 ih2 =>
    intro hs hc
    have hce := codeSiteLe_of_code hc (cut_entry_code cut)
    obtain ⟨a', a, h1⟩ := ih1 (hc _ _ _ _ find) (codeSiteLe_of_code hce rfl)
    have he := cut_entry_code cut
    have hpost : post.code = s.code := (body.code hdom).trans he
    obtain ⟨b', b, h2⟩ := ih2 hs.2.2 (codeSiteLe_of_code hc ((setVars_code _ _ _).trans hpost))
    have := hs.1
    exact ⟨_, .callRetCont (exceptionName := exceptionName) (liveOut := liveOut) args find nodup cut a lengths b,
      by simp only; omega⟩
  | @callHandle l s names live target arguments exceptionName handlerProgram continuation liveOut values env prog
      entry exn post wb output wh args find nodup cut body _ ih1 ih2 =>
    intro hs hc
    have hce := codeSiteLe_of_code hc (cut_entry_code cut)
    obtain ⟨a', a, h1⟩ := ih1 (hc _ _ _ _ find) (codeSiteLe_of_code hce rfl)
    have he := cut_entry_code cut
    have hpost : post.code = s.code := (body.code hdom).trans he
    obtain ⟨b', b, h2⟩ := ih2 hs.2.1 (codeSiteLe_of_code hc (by exact hpost))
    have := hs.1
    exact ⟨_, .callHandle (continuation := continuation) (liveOut := liveOut) args find nodup cut a b,
      by simp only; omega⟩

#print axioms LoopWorkPL.site_mono
end InitECandidate.Runtime.FineCost
