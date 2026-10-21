import InitECandidate.Runtime.LoopWordPLLeaf
import InitECandidate.Runtime.LoopWordPL
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend

/-! The WordSimp-source price `bP c (surOf T2 + surOf T1)` is dominated by a
label-indexed Loop price: a returning call pays the table entries at its own
return label, a tail call the largest entries of its target. -/

/-- Largest table entry whose key satisfies `P`. -/
def tabMax (T : SiteTable) (P : Nat × Nat × List Nat → Bool) : Nat :=
  T.foldl (fun m e => if P e.1 then max m e.2 else m) 0

theorem tabMax_aux (P : Nat × Nat × List Nat → Bool) : ∀ (T : SiteTable) (m : Nat),
    m ≤ T.foldl (fun m e => if P e.1 then max m e.2 else m) m ∧
      ∀ e ∈ T, P e.1 = true → e.2 ≤ T.foldl (fun m e => if P e.1 then max m e.2 else m) m
  | [], m => ⟨Nat.le_refl _, fun _ h => by cases h⟩
  | e :: T, m => by
    simp only [List.foldl_cons]
    have ih := tabMax_aux P T (if P e.1 then max m e.2 else m)
    refine ⟨Nat.le_trans (by split <;> omega) ih.1, fun e' he' hk => ?_⟩
    rcases List.mem_cons.1 he' with rfl | he'
    · exact Nat.le_trans (by simp [hk]) ih.1
    · exact ih.2 e' he' hk

theorem tLookup_le_tabMax (T : SiteTable) (P : Nat × Nat × List Nat → Bool) (key : Nat × Nat × List Nat)
    (hP : P key = true) : tLookup T key ≤ tabMax T P := by
  unfold tLookup
  split
  · rename_i e he
    have hk := List.find?_some he
    simp only [beq_iff_eq] at hk
    exact (tabMax_aux P T 0).2 e (List.mem_of_find?_eq_some he) (by rw [hk]; exact hP)
  · exact Nat.zero_le _

/-- Site-key destination code of a tail call. -/
def destKey : Option Nat → Nat
  | none => 0
  | some d => d + 1

/-- Largest tail-call entry for a destination. -/
def tailEnv (T : SiteTable) (d : Option Nat) : Nat :=
  tabMax T (fun k => k.1 == 1 && k.2.1 == destKey d)

/-- The label-indexed Loop price dominating `bP c (surOf T2 + surOf T1)`. -/
noncomputable def wsLoopPrice (c : Compiler.Encoders.Asm.AsmConfigExact 64) (T1 T2 : SiteTable) : LoopPriceL where
  base :=
    { leaf := leafPL c T1 T2
      ite := 29
      iter := 14
      call := 189
      argCost := fun n => 39 * (n + 1 - 22)
      ret := 0
      cont := 6 }
  site := fun l _ => 24 * (tLookup T2 (0, l.1, [l.2]) + tLookup T1 (0, l.1, [l.2]))
  tail := fun d => 24 * (tailEnv T2 d + tailEnv T1 d)
  retNames := fun n => 21 * (n + 1 - 22)

theorem surOf_tail_le (T : SiteTable) (d : Option Nat) (args : List Nat)
    (h : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat)) :
    surOf T (.call none d args h) ≤ tailEnv T d := by
  simp only [surOf, siteKey, tailEnv]
  exact tLookup_le_tabMax T _ _ (by cases d <;> simp [destKey])

/-- `bP c (surOf T2 + surOf T1)` is dominated by `wsLoopPrice c T1 T2`. -/
noncomputable def wsDominates {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) (T1 T2 : SiteTable) :
    WordDominatesL (C := C) (F := F) (bP c (fun q => surOf T2 q + surOf T1 q)) (wsLoopPrice c T1 T2) where
  T := 6
  I := 23
  L := 2
  U := 189
  argW := fun n => 39 * (n + 1 - 22)
  R := 0
  seqZero := fun a b s => bP_seq_zero c T1 T2 a b s
  skipZero := fun s => by
    simp [bP, preIselPrice, wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
      WordToStack.refinedWordStackLeafBudget, surOf, siteKey]
  tick := fun s => by
    simp [bP, preIselPrice, wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
      WordToStack.refinedWordStackLeafBudget, surOf, siteKey]
  ite := fun _ _ _ _ _ s => by
    simp [bP, preIselPrice, wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
      WordToStack.refinedWordStackLeafBudget, surOf, siteKey]
  loop := fun _ _ _ s => by
    simp [bP, preIselPrice, wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
      WordToStack.refinedWordStackLeafBudget, surOf, siteKey]
  leafOk := fun ctxt p l s cost leaf => bP_leafOk c T1 T2 ctxt p l s cost leaf
  tailCall := fun d args h s => by
    have h2 := surOf_tail_le T2 d args h
    have h1 := surOf_tail_le T1 d args h
    simp only [bP, preIselPrice, wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
      WordToStack.refinedWordStackLeafBudget, wsLoopPrice]
    omega
  retCall := fun rets cut rc l1 l2 d args h s => by
    simp only [bP, preIselPrice, wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice,
      WordToStack.refinedWordStackLeafBudget, wsLoopPrice, surOf, siteKey]
    split <;> omega
  iteOk := by simp [wsLoopPrice]
  iterOk := by simp [wsLoopPrice]
  tailOk := by simp [wsLoopPrice]
  argOk := fun n => Nat.le_refl _
  retOk := Nat.le_refl _
  contOk := by simp [wsLoopPrice]

/-- Loop-to-Word at the WordSimp-source price: from any related Word state,
the program compiled at label `l` costs at most its `LoopWorkPL` work under
`wsLoopPrice`. -/
theorem loop_to_word_cost_ws {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) (T1 T2 : SiteTable)
    {l : Nat × Nat} {s : LoopSemStateFiniteExact 64 F} {p : HolLoopProg 64} {output w}
    (work : LoopWorkPL (wsLoopPrice c T1 T2) l s p output w) :
    WordCostLePL C (bP c (fun q => surOf T2 q + surOf T1 q)) s p l output w :=
  loop_to_word_costPL (wsDominates c T1 T2) work

#print axioms loop_to_word_cost_ws
end InitECandidate.Runtime.FineCost
