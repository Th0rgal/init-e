import InitECandidate.Runtime.SourceCostLoopOptimiseG
import InitECandidate.Runtime.LoopWordPLInstance
import InitECandidate.Runtime.LoopWordPLCallTab
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

/-! The selector-derived Loop price for the optimisation passes: leaves pay
`leafPL`; a returning call pays the caller+callee table entry, a tail call the
callee's tail envelope, a call stopped before its callee the largest of them.
Its function-indexed work transfers to labelled work at the WordSimp-source
price `wsLoopPrice` with no increase. -/

/-- The WordSimp tail surcharge for a static target. -/
def wsTail (d : Option Nat) : Nat := 24 * (tailEnv wsT2 d + tailEnv wsT1 d)

/-- Largest caller+callee table entry. -/
def callTabMax : Nat := callTab.foldl (fun m e => max m e.2) 0

/-- Largest tail envelope of either table. -/
def tailMax : Nat := tabMax wsT2 (fun k => k.1 == 1) + tabMax wsT1 (fun k => k.1 == 1)

/-- `leafPL` as a pass leaf price. -/
noncomputable def wsLeaf (c : Compiler.Encoders.Asm.AsmConfigExact 64) : LeafPrice where
  lf := leafPL c wsT1 wsT2
  dom := fun p w h => by
    unfold leafPL at h
    split at h
    · cases h
    · rename_i x hx; simp [hx]
  skip := by
    simp [leafPL, loopWorkLeafCost, LoopToWord.compHOL, lineBound, isLeafProg, leafNodeB, isExprStmt, nodeEnv,
      siteKey, preAllocLeafBudget, WordToStack.refinedWordStackLeafBudget]
  ffiLive := fun f a b c' d l l' => by
    simp [leafPL, loopWorkLeafCost, LoopToWord.compHOL, lineBound, isLeafProg, leafNodeB, isExprStmt, nodeEnv,
      siteKey, preAllocLeafBudget, WordToStack.refinedWordStackLeafBudget]
  cs := fun f g => 24 * (callTabGet (f, some g) + callTabGet (f, none))
  ts := fun g => wsTail (some g) + wsTail none
  rn := fun n => 21 * (n + 1 - 22)
  shortC := 24 * callTabMax + 24 * tailMax
  ite := 29
  iteOne := by decide
  iter := 14
  call := 189
  cont := 6
  argCost := fun n => 39 * (n + 1 - 22)
  argMono := fun m n h => by omega
  ret := 0

theorem tabMax_le_of (T : SiteTable) (P Q : Nat × Nat × List Nat → Bool) (h : ∀ k, P k = true → Q k = true) :
    tabMax T P ≤ tabMax T Q := by
  unfold tabMax
  suffices ∀ (T : SiteTable) (m1 m2 : Nat), m1 ≤ m2 →
      T.foldl (fun m e => if P e.1 then max m e.2 else m) m1 ≤ T.foldl (fun m e => if Q e.1 then max m e.2 else m) m2 from
    this T 0 0 (Nat.le_refl _)
  intro T
  induction T with
  | nil => intro m1 m2 h12; exact h12
  | cons e T ih =>
    intro m1 m2 h12
    simp only [List.foldl_cons]
    apply ih
    by_cases hp : P e.1 = true
    · simp only [hp, h _ hp, ↓reduceIte]; omega
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]; split <;> omega

theorem wsTail_le (d : Option Nat) : wsTail d ≤ 24 * tailMax := by
  have h2 := tabMax_le_of wsT2 (fun k => k.1 == 1 && k.2.1 == destKey d) (fun k => k.1 == 1)
    (fun k h => by simp only [Bool.and_eq_true] at h; exact h.1)
  have h1 := tabMax_le_of wsT1 (fun k => k.1 == 1 && k.2.1 == destKey d) (fun k => k.1 == 1)
    (fun k h => by simp only [Bool.and_eq_true] at h; exact h.1)
  simp only [wsTail, tailEnv, tailMax]; omega

theorem callTab_le_max (k : Nat × Option Nat) : callTabGet k ≤ callTabMax := by
  unfold callTabGet callTabMax
  split
  · rename_i e he
    have mem := List.mem_of_find?_eq_some he
    suffices ∀ (T : List ((Nat × Option Nat) × Nat)) (m : Nat), (m ≤ T.foldl (fun m e => max m e.2) m) ∧
        ∀ e ∈ T, e.2 ≤ T.foldl (fun m e => max m e.2) m from (this callTab 0).2 e mem
    intro T
    induction T with
    | nil => intro m; exact ⟨Nat.le_refl _, fun _ h => by cases h⟩
    | cons x T ih =>
      intro m
      simp only [List.foldl_cons]
      refine ⟨Nat.le_trans (Nat.le_max_left _ _) (ih _).1, fun e' he' => ?_⟩
      rcases List.mem_cons.1 he' with rfl | he'
      · exact Nat.le_trans (Nat.le_max_right _ _) (ih _).1
      · exact (ih _).2 e' he'
  · exact Nat.zero_le _

theorem labAfterS_fst : ∀ (p : HolLoopProg 64) (l : Nat × Nat), (labAfterS p l).1 = l.1
  | .seq a b, l => by show (labAfterS b (labAfterS a l)).1 = _; rw [labAfterS_fst b, labAfterS_fst a]
  | .ite _ _ _ y n _, l => by show (labAfterS n (labAfterS y l)).1 = _; rw [labAfterS_fst n, labAfterS_fst y]
  | .loop _ b _, l => labAfterS_fst b l
  | .mark b, l => labAfterS_fst b l
  | .call (some _) _ _ none, l => rfl
  | .call (some _) _ _ (some (_, p1, p2, _)), l => by
    show (labAfterS p2 (labAfterS p1 (l.1, l.2 + 1))).1 = _; rw [labAfterS_fst p2, labAfterS_fst p1]
  | .call none _ _ _, _ | .skip, _ | .assign _ _, _ | .store _ _, _ | .setGlobal _ _, _ | .load32 _ _, _
  | .loadByte _ _, _ | .store32 _ _, _ | .storeByte _ _, _ | .break _, _ | .continue _, _ | .raise _, _
  | .return _, _ | .shMem _ _ _, _ | .tick, _ | .fail, _ | .locValue _ _, _ | .ffi _ _ _ _ _ _, _
  | .primitive _ _ _, _ | .arith _, _ => rfl

theorem labAfter_fst (p : HolLoopProg 64) (l : Nat × Nat) : (labAfter p l).1 = l.1 := by
  rw [← labAfterS_eq]; exact labAfterS_fst p l

theorem calleeName_loopCallee (t : Option Nat) (v : List (WordLocW 64)) : calleeName t v = loopCallee t v := by
  cases t <;> rfl

#print axioms callTab_le_max

theorem site_le_cs (c : Compiler.Encoders.Asm.AsmConfigExact 64) {l : Nat × Nat} {f : Nat} {t : Option Nat}
    (v : List (WordLocW 64)) (hs : siteA l t ≤ siteB l t) (hf : l.1 = f) :
    siteA l t ≤ (wsLeaf c).cs f (loopCallee t v) := by
  subst hf
  cases t <;> simp only [siteB, wsLeaf, loopCallee] at hs ⊢ <;> omega

theorem tail_le_ts (c : Compiler.Encoders.Asm.AsmConfigExact 64) (t : Option Nat) (v : List (WordLocW 64)) :
    wsTail t ≤ (wsLeaf c).ts (loopCallee t v) := by
  cases t <;> simp only [wsLeaf, loopCallee] <;> omega

theorem ws_dom (c : Compiler.Encoders.Asm.AsmConfigExact 64) :
    ∀ p w, (wsLoopPrice c wsT1 wsT2).base.leaf p = some w → (loopWorkLeafCost p).isSome = true :=
  fun p w h => (wsLeaf c).dom p w h

/-- Function-indexed optimised Loop work at the selector-derived price, from a
label in the same function where the program passes the site walk and every
callee body is certified, is labelled work at the WordSimp-source price with
no increase. -/
theorem LoopWorkG.toPL {F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) {f : Nat}
    {s : LoopSemStateFiniteExact 64 F} {p : HolLoopProg 64} {output} {w : Nat}
    (work : LoopWorkG (wsLeaf c) f s p output w) :
    ∀ l : Nat × Nat, l.1 = f → SiteLe siteA siteB l p → CodeSiteLe siteA siteB s →
      ∃ w', LoopWorkPL (wsLoopPrice c wsT1 wsT2) l s p output w' ∧ w' ≤ w := by
  have hIte : (wsLeaf c).ite = 29 := rfl
  have hIter : (wsLeaf c).iter = 14 := rfl
  have hCall : (wsLeaf c).call = 189 := rfl
  have hCont : (wsLeaf c).cont = 6 := rfl
  have hRet : (wsLeaf c).ret = 0 := rfl
  have hArg : ∀ n, (wsLeaf c).argCost n = 39 * (n + 1 - 22) := fun _ => rfl
  induction work with
  | atom leaf run => intro l _ _ _; exact ⟨_, .atom leaf run, Nat.le_refl _⟩
  | mark _ ih =>
    intro l hf hs hc; obtain ⟨w', a, h⟩ := ih l hf hs hc; exact ⟨w', .mark a, h⟩
  | @seqNext f s first second middle output a b _ _ ih1 ih2 =>
    intro l hf hs hc
    obtain ⟨a', x, h1⟩ := ih1 l hf hs.1 hc
    obtain ⟨b', y, h2⟩ := ih2 (labAfter first l) (by rw [labAfter_fst]; exact hf) hs.2
      (codeSiteLe_of_code hc (x.code (ws_dom c)))
    exact ⟨_, .seqNext x y, by omega⟩
  | seqStop _ ih =>
    intro l hf hs hc; obtain ⟨w', a, h⟩ := ih l hf hs.1 hc; exact ⟨w', .seqStop a, h⟩
  | @iteBranch f s operator register right yes no live x y output w lhs rhs _ ih =>
    intro l hf hs hc
    have hb : SiteLe siteA siteB (if Compiler.Encoders.Asm.wordCmpHOL operator x y then l else labAfter yes l)
        (if Compiler.Encoders.Asm.wordCmpHOL operator x y then yes else no) := by
      split
      · exact hs.1
      · exact hs.2
    have hfb : (if Compiler.Encoders.Asm.wordCmpHOL operator x y then l else labAfter yes l).1 = f := by
      split
      · exact hf
      · rw [labAfter_fst]; exact hf
    obtain ⟨w', a, h⟩ := ih _ hfb hb hc
    exact ⟨_, .iteBranch lhs rhs a, by simp only [hArg, hCall, hRet, hCont, wsLoopPrice]; omega⟩
  | iteInvalid invalid => intro l _ _ _; exact ⟨1, .iteInvalid invalid, Nat.le_refl _⟩
  | loopNext cut _ again _ ih1 ih2 =>
    intro l hf hs hc
    have hce := codeSiteLe_of_code hc (cut_entry_code cut)
    obtain ⟨a', x, h1⟩ := ih1 l hf hs hce
    obtain ⟨b', y, h2⟩ := ih2 l hf hs (codeSiteLe_of_code hce (x.code (ws_dom c)))
    exact ⟨_, .loopNext cut x again y, by simp only [hArg, hCall, hRet, hCont, wsLoopPrice]; omega⟩
  | loopBreak cut _ ih =>
    intro l hf hs hc
    obtain ⟨a', x, h⟩ := ih l hf hs (codeSiteLe_of_code hc (cut_entry_code cut))
    exact ⟨_, .loopBreak cut x, by simp only [hArg, hCall, hRet, hCont, wsLoopPrice]; omega⟩
  | loopExit cut _ stop ih =>
    intro l hf hs hc
    obtain ⟨a', x, h⟩ := ih l hf hs (codeSiteLe_of_code hc (cut_entry_code cut))
    exact ⟨_, .loopExit cut x stop, by simp only [hArg, hCall, hRet, hCont, wsLoopPrice]; omega⟩
  | loopCut stopped => intro l _ _ _; exact ⟨_, .loopCut stopped, by simp only [hArg, hCall, hRet, hCont, wsLoopPrice]; omega⟩
  | @callShort f s returns target arguments handler output short run =>
    intro l hf hs _
    refine ⟨_, .callShort short run, ?_⟩
    rcases returns with _ | ⟨names, live⟩
    · have := wsTail_le target
      simp only [hArg, hCall, hRet, hCont, wsLoopPrice, wsLeaf, LeafPrice.rnOpt, wsTail] at this ⊢; omega
    · have h1 : siteA l target ≤ siteB l target := by unfold SiteLe at hs; exact hs.1
      have h2 := callTab_le_max (l.1, target)
      simp only [siteB] at h1
      have h3 : (wsLoopPrice c wsT1 wsT2).site l target = siteA l target := rfl
      simp only [hArg, hCall, hRet, hCont, wsLoopPrice, wsLeaf, LeafPrice.rnOpt] at h3 ⊢; omega
  | @callTail f s target arguments handler values env prog result post wb args find noHandler clock _ ih =>
    intro l hf hs hc
    obtain ⟨a', x, h⟩ := ih (calleeName target values, 2) (calleeName_loopCallee target values)
      (hc _ _ _ _ find) (codeSiteLe_of_code hc rfl)
    have ht := tail_le_ts c target values
    refine ⟨_, .callTail args find noHandler clock x, ?_⟩
    simp only [hArg, hCall, hRet, hCont, wsLoopPrice, wsTail] at ht ⊢; omega
  | @callRet f s names live target arguments handler values env prog entry result post wb args find nodup cut _
      plain ih =>
    intro l hf hs hc
    have hce := codeSiteLe_of_code hc (cut_entry_code cut)
    obtain ⟨a', x, h⟩ := ih (calleeName target values, 2) (calleeName_loopCallee target values)
      (hc _ _ _ _ find) (codeSiteLe_of_code hce rfl)
    have h1 : siteA l target ≤ siteB l target := by unfold SiteLe at hs; exact hs.1
    have hcs := site_le_cs c values h1 hf
    have h3 : (wsLoopPrice c wsT1 wsT2).site l target = siteA l target := rfl
    refine ⟨_, .callRet args find nodup cut x plain, ?_⟩
    simp only [hArg, hCall, hRet, hCont, wsLoopPrice, wsLeaf] at h3 hcs ⊢; omega
  | @callRetCont f s names live target arguments exceptionName handlerProgram continuation liveOut values env
      prog entry returned post wb output wc args find nodup cut _ lengths _ ih1 ih2 =>
    intro l hf hs hc
    have hce := codeSiteLe_of_code hc (cut_entry_code cut)
    obtain ⟨a', x, h1⟩ := ih1 (calleeName target values, 2) (calleeName_loopCallee target values)
      (hc _ _ _ _ find) (codeSiteLe_of_code hce rfl)
    have he := cut_entry_code cut
    have hpost : post.code = s.code := (x.code (ws_dom c)).trans he
    obtain ⟨b', y, h2⟩ := ih2 (labAfter handlerProgram (l.1, l.2 + 1)) (by rw [labAfter_fst]; exact hf) hs.2.2
      (codeSiteLe_of_code hc ((setVars_code _ _ _).trans hpost))
    have hsa : siteA l target ≤ siteB l target := hs.1
    have hcs := site_le_cs c values hsa hf
    have h3 : (wsLoopPrice c wsT1 wsT2).site l target = siteA l target := rfl
    refine ⟨_, .callRetCont (exceptionName := exceptionName) (liveOut := liveOut) args find nodup cut x lengths y, ?_⟩
    simp only [hArg, hCall, hRet, hCont, wsLoopPrice, wsLeaf] at h3 hcs ⊢; omega
  | @callHandle f s names live target arguments exceptionName handlerProgram continuation liveOut values env prog
      entry exn post wb output wh args find nodup cut _ _ ih1 ih2 =>
    intro l hf hs hc
    have hce := codeSiteLe_of_code hc (cut_entry_code cut)
    obtain ⟨a', x, h1⟩ := ih1 (calleeName target values, 2) (calleeName_loopCallee target values)
      (hc _ _ _ _ find) (codeSiteLe_of_code hce rfl)
    have he := cut_entry_code cut
    have hpost : post.code = s.code := (x.code (ws_dom c)).trans he
    obtain ⟨b', y, h2⟩ := ih2 (l.1, l.2 + 1) hf hs.2.1 (codeSiteLe_of_code hc (by exact hpost))
    have hsa : siteA l target ≤ siteB l target := hs.1
    have hcs := site_le_cs c values hsa hf
    have h3 : (wsLoopPrice c wsT1 wsT2).site l target = siteA l target := rfl
    refine ⟨_, .callHandle (continuation := continuation) (liveOut := liveOut) args find nodup cut x y, ?_⟩
    simp only [hArg, hCall, hRet, hCont, wsLoopPrice, wsLeaf] at h3 hcs ⊢; omega

#print axioms LoopWorkG.toPL
end InitECandidate.Runtime.FineCost
