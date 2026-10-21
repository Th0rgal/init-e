import InitECandidate.Runtime.SourceCostLoopOptimiseG
import InitECandidate.Runtime.LoopWordPLInstance
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.LoopSemStateFiniteExact

/-! The selector-derived Loop leaf price `leafPL` as a `LeafPrice`, and the
transfer of its optimised Loop work to `LoopWorkP` at the WordSimp-source base
prices of `wsLoopPrice` (each base constant is at most the `LoopWork` one). -/

/-- `leafPL` as a pass leaf price. -/
noncomputable def wsLeaf (c : Compiler.Encoders.Asm.AsmConfigExact 64) (T1 T2 : SiteTable) : LeafPrice where
  lf := leafPL c T1 T2
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

/-- Work at the `LoopWork` constants with leaf price `L` is work at the
cheaper `wsLoopPrice` base constants, at no greater total. -/
theorem LoopWorkG.toWs {F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) (T1 T2 : SiteTable)
    {s : LoopSemStateFiniteExact 64 F} {p : HolLoopProg 64} {output} {w : Nat}
    (work : LoopWorkG (wsLeaf c T1 T2) s p output w) :
    ∃ w', w' ≤ w ∧ LoopWorkP (wsLoopPrice c T1 T2).base s p output w' := by
  induction work with
  | atom leaf run => exact ⟨_, Nat.le_refl _, .atom leaf run⟩
  | mark _ ih => obtain ⟨w', h, i⟩ := ih; exact ⟨w', h, .mark i⟩
  | seqNext _ _ ih1 ih2 =>
    obtain ⟨a, h1, i1⟩ := ih1; obtain ⟨b, h2, i2⟩ := ih2; exact ⟨a + b, by omega, .seqNext i1 i2⟩
  | seqStop _ ih => obtain ⟨a, h, i⟩ := ih; exact ⟨a, h, .seqStop i⟩
  | iteBranch lhs rhs _ ih =>
    obtain ⟨a, h, i⟩ := ih; exact ⟨_, by simp only [wsLoopPrice]; omega, .iteBranch lhs rhs i⟩
  | iteInvalid invalid => exact ⟨1, Nat.le_refl _, .iteInvalid invalid⟩
  | loopNext cut _ again _ ih1 ih2 =>
    obtain ⟨a, h1, i1⟩ := ih1; obtain ⟨b, h2, i2⟩ := ih2
    exact ⟨_, by simp only [wsLoopPrice]; omega, .loopNext cut i1 again i2⟩
  | loopBreak cut _ ih =>
    obtain ⟨a, h, i⟩ := ih; exact ⟨_, by simp only [wsLoopPrice]; omega, .loopBreak cut i⟩
  | loopExit cut _ stop ih =>
    obtain ⟨a, h, i⟩ := ih; exact ⟨_, by simp only [wsLoopPrice]; omega, .loopExit cut i stop⟩
  | loopCut stopped => exact ⟨_, by simp only [wsLoopPrice]; omega, .loopCut stopped⟩
  | callShort short run => exact ⟨_, by simp only [wsLoopPrice]; omega, .callShort short run⟩
  | callTail args find noHandler clock _ ih =>
    obtain ⟨a, h, i⟩ := ih; exact ⟨_, by simp only [wsLoopPrice]; omega, .callTail args find noHandler clock i⟩
  | callRet args find nodup cut _ plain ih =>
    obtain ⟨a, h, i⟩ := ih; exact ⟨_, by simp only [wsLoopPrice]; omega, .callRet args find nodup cut i plain⟩
  | callRetCont args find nodup cut _ lengths _ ih1 ih2 =>
    obtain ⟨a, h1, i1⟩ := ih1; obtain ⟨b, h2, i2⟩ := ih2
    exact ⟨_, by simp only [wsLoopPrice]; omega, .callRetCont args find nodup cut i1 lengths i2⟩
  | callHandle args find nodup cut _ _ ih1 ih2 =>
    obtain ⟨a, h1, i1⟩ := ih1; obtain ⟨b, h2, i2⟩ := ih2
    exact ⟨_, by simp only [wsLoopPrice]; omega, .callHandle args find nodup cut i1 i2⟩

#print axioms LoopWorkG.toWs
end InitECandidate.Runtime.FineCost
