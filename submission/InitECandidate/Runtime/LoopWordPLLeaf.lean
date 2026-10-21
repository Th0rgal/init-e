import InitECandidate.Runtime.LoopWordPLLeafRen
import InitECandidate.Runtime.WordSimpCert
import InitECandidate.Runtime.WordLineCost
import InitECandidate.Runtime.SourceCostLoopWork
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend

/-! Loop leaves under the WordSimp-source price `bP c (surOf T2 + surOf T1)`.
A compiled leaf is straight-line Word code; each node pays its exact selector
price (context-independent by `LoopWordPLLeafRen`) plus 24 per tabled constant
re-insert, bounded per site kind since leaf site keys name Word variables. -/

/-- Largest table entry of a site kind. -/
def kindMax (T : SiteTable) (k : Nat) : Nat :=
  T.foldl (fun m e => if e.1.1 = k then max m e.2 else m) 0

theorem kindMax_aux (k : Nat) : ∀ (T : SiteTable) (m : Nat),
    m ≤ T.foldl (fun m e => if e.1.1 = k then max m e.2 else m) m ∧
      ∀ e ∈ T, e.1.1 = k → e.2 ≤ T.foldl (fun m e => if e.1.1 = k then max m e.2 else m) m
  | [], m => ⟨Nat.le_refl _, fun _ h => by cases h⟩
  | e :: T, m => by
    simp only [List.foldl_cons]
    have ih := kindMax_aux k T (if e.1.1 = k then max m e.2 else m)
    refine ⟨Nat.le_trans (by split <;> omega) ih.1, fun e' he' hk => ?_⟩
    rcases List.mem_cons.1 he' with rfl | he'
    · exact Nat.le_trans (by simp [hk]) ih.1
    · exact ih.2 e' he' hk

theorem tLookup_le_kindMax (T : SiteTable) (key : Nat × Nat × List Nat) : tLookup T key ≤ kindMax T key.1 := by
  unfold tLookup
  split
  · rename_i e he
    have hmem := List.mem_of_find?_eq_some he
    have hk := List.find?_some he
    simp only [beq_iff_eq] at hk
    exact (kindMax_aux key.1 T 0).2 e hmem (by rw [hk])
  · exact Nat.zero_le _

/-- Per-node surcharge envelope: the largest entry of the node's site kind. -/
def nodeEnv (T : SiteTable) (p : WordLangProgHOL (BitVec 64)) : Nat :=
  match siteKey p with
  | some key => kindMax T key.1
  | none => 0

theorem surOf_le_nodeEnv (T : SiteTable) (p : WordLangProgHOL (BitVec 64)) : surOf T p ≤ nodeEnv T p := by
  unfold surOf nodeEnv
  cases siteKey p with
  | none => exact Nat.le_refl _
  | some key => exact tLookup_le_kindMax T key

/-- Static leaf budget of a Word node under `bP`. -/
def leafNodeB (c : Compiler.Encoders.Asm.AsmConfigExact 64) (T1 T2 : SiteTable)
    (p : WordLangProgHOL (BitVec 64)) : Option Nat :=
  (if isExprStmt p then some (iselX c p) else preAllocLeafBudget p).map (· + 24 * (nodeEnv T2 p + nodeEnv T1 p))

theorem preIsel_le_node {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) (p : WordLangProgHOL (BitVec 64))
    (n : Nat) (h : (if isExprStmt p then some (iselX c p) else preAllocLeafBudget p) = some n)
    (s : WordSemStateFiniteExact 64 C F) : preIselPrice c p s ≤ n := by
  cases p <;> simp only [isExprStmt, if_true, if_false, Bool.false_eq_true, Option.some.injEq] at h
  all_goals first
    | (subst h; exact Nat.le_refl _)
    | (simp only [preIselPrice, wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice, preAllocLeafBudget, rawMovePrice,
        Option.map_eq_some_iff] at h ⊢
       first
        | omega
        | (obtain ⟨b, hb, rfl⟩ := h; simp only [hb]; omega)
        | (rw [h])
        | (simp_all))

theorem bP_le_leafNodeB {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) (T1 T2 : SiteTable)
    (p : WordLangProgHOL (BitVec 64)) (n : Nat) (h : leafNodeB c T1 T2 p = some n)
    (s : WordSemStateFiniteExact 64 C F) : bP c (fun q => surOf T2 q + surOf T1 q) p s ≤ n := by
  unfold leafNodeB at h
  rcases hb : (if isExprStmt p then some (iselX c p) else preAllocLeafBudget p) with _ | b
  · rw [hb] at h; cases h
  · rw [hb] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    have h1 := preIsel_le_node c p b hb s
    have h2 := surOf_le_nodeEnv T2 p
    have h3 := surOf_le_nodeEnv T1 p
    simp only [bP]
    omega

theorem bP_seq_zero {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) (T1 T2 : SiteTable)
    (a b : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F) :
    bP c (fun q => surOf T2 q + surOf T1 q) (.seq a b) s = 0 := by
  simp [bP, preIselPrice, wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice, WordToStack.refinedWordStackLeafBudget,
    surOf, siteKey]

/-- Straight-line code costs at most its static `leafNodeB` line bound. -/
theorem bP_cost_le_line {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) (T1 T2 : SiteTable)
    (p : WordLangProgHOL (BitVec 64)) (n : Nat) (h : lineBound (leafNodeB c T1 T2) p = some n)
    (s : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost (bP c (fun q => surOf T2 q + surOf T1 q)) p s ≤ n :=
  wordCost_le_lineBound _ _ (bP_seq_zero c T1 T2) (fun p s n _ h => bP_le_leafNodeB c T1 T2 p n h s) p n h s

#print axioms bP_cost_le_line

/-- Loop leaf price: the static line bound of the leaf compiled in the empty
context (every context gives the same bound, `leaf_ctxt`). -/
noncomputable def leafPL (c : Compiler.Encoders.Asm.AsmConfigExact 64) (T1 T2 : SiteTable)
    (q : HolLoopProg 64) : Option Nat :=
  match loopWorkLeafCost q with
  | none => none
  | some _ => lineBound (leafNodeB c T1 T2) (LoopToWord.compHOL (.ln : Spt Nat) q (0, 0)).1

theorem leaf_ctxt (c : Compiler.Encoders.Asm.AsmConfigExact 64) (T1 T2 : SiteTable) (q : HolLoopProg 64)
    (hq : (loopWorkLeafCost q).isSome = true) (ctxt : Spt Nat) (l : Nat × Nat) :
    lineBound (leafNodeB c T1 T2) (LoopToWord.compHOL ctxt q l).1 =
      lineBound (leafNodeB c T1 T2) (LoopToWord.compHOL (.ln : Spt Nat) q (0, 0)).1 := by
  cases q <;> simp only [loopWorkLeafCost, Option.isSome_none, Option.isSome_some, Bool.false_eq_true] at hq
  case assign n e =>
    simp only [LoopToWord.compHOL, lineBound, isLeafProg, leafNodeB, isExprStmt, if_true, nodeEnv, siteKey]
    rw [iselX_assign c (eraseV_compExp ctxt .ln e) _ (LoopToWord.findVarHOL .ln n)]
  case store e v =>
    simp only [LoopToWord.compHOL, lineBound, isLeafProg, leafNodeB, isExprStmt, if_true, nodeEnv, siteKey]
    rw [iselX_store c (eraseV_compExp ctxt .ln e) _ (LoopToWord.findVarHOL .ln v)]
  case setGlobal a e =>
    simp only [LoopToWord.compHOL, lineBound, isLeafProg, leafNodeB, isExprStmt, if_true, nodeEnv, siteKey]
    rw [iselX_set c (eraseV_compExp ctxt .ln e)]
  case shMem op n e =>
    simp only [LoopToWord.compHOL, lineBound, isLeafProg, leafNodeB, isExprStmt, if_true, nodeEnv, siteKey]
    rw [iselX_share c (eraseV_compExp ctxt .ln e) op _ (LoopToWord.findVarHOL .ln n)]
  case arith op => cases op <;> simp [LoopToWord.compHOL, lineBound, isLeafProg, leafNodeB, isExprStmt, nodeEnv,
    siteKey, preAllocLeafBudget, WordToStack.refinedWordStackLeafBudget,
      Compiler.Encoders.Asm.HolInst.ofWordLangInst, Compiler.Encoders.Asm.HolArith.ofWordLangArith,
      WordToStack.refinedNativeInstructionPrice]
  case primitive ds op args =>
    cases op
    rcases ds with _ | ⟨d1, _ | ⟨d2, _ | ⟨d3, ds⟩⟩⟩ <;>
      rcases args with _ | ⟨a1, _ | ⟨a2, _ | ⟨a3, _ | ⟨a4, args⟩⟩⟩⟩ <;>
      simp only [LoopToWord.compHOL]
    simp only [lineBound, isLeafProg, leafNodeB, isExprStmt, if_true, nodeEnv, siteKey]
    rw [iselX_assign c (e := .var (LoopToWord.findVarHOL ctxt a3)) (e' := .var (LoopToWord.findVarHOL .ln a3)) rfl 1 1,
      iselX_assign c (e := .var 1) (e' := .var 1) rfl (LoopToWord.findVarHOL ctxt d2) (LoopToWord.findVarHOL .ln d2),
      iselX_assign c (e := .var 3) (e' := .var 3) rfl (LoopToWord.findVarHOL ctxt d1) (LoopToWord.findVarHOL .ln d1)]
    simp [preAllocLeafBudget, WordToStack.refinedWordStackLeafBudget,
      Compiler.Encoders.Asm.HolInst.ofWordLangInst, Compiler.Encoders.Asm.HolArith.ofWordLangArith,
      WordToStack.refinedNativeInstructionPrice]
  all_goals try simp only [LoopToWord.compHOL]
  all_goals
    simp [lineBound, isLeafProg, leafNodeB, isExprStmt, nodeEnv, siteKey, preAllocLeafBudget,
      WordToStack.refinedWordStackLeafBudget,
      Compiler.Encoders.Asm.HolInst.ofWordLangInst, Compiler.Encoders.Asm.HolArith.ofWordLangArith,
      WordToStack.refinedNativeInstructionPrice]

/-- `leafOk` for the WordSimp-source price: a compiled Loop leaf, in any
variable context and at any label, costs at most `leafPL`. -/
theorem bP_leafOk {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) (T1 T2 : SiteTable)
    (ctxt : Spt Nat) (q : HolLoopProg 64) (l : Nat × Nat) (s : WordSemStateFiniteExact 64 C F) (cost : Nat)
    (h : leafPL c T1 T2 q = some cost) :
    wordExecutionCost (bP c (fun q => surOf T2 q + surOf T1 q)) (LoopToWord.compHOL ctxt q l).1 s ≤ cost := by
  unfold leafPL at h
  split at h
  · cases h
  · rename_i w hq
    rw [← leaf_ctxt c T1 T2 q (by simp [hq]) ctxt l] at h
    exact bP_cost_le_line c T1 T2 _ cost h s

#print axioms bP_leafOk
end InitECandidate.Runtime.FineCost
