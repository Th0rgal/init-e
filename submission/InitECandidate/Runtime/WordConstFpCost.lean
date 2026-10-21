import InitECandidate.Runtime.WordSimpCost
import InitECandidate.Runtime.WordIselAll
import InitECandidate.Runtime.WordExecutionCostProps
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact Flapjack.Compiler.Backend.WordSimp

/-! Cost transfer for WordSimp's constant folding (`constFp`). The folded
program pays the exact selector price `preIselPrice c`; the source pays it plus
24 per constant re-assignment that `dropConsts` emits before a call, alloc, ffi
or install, as a node surcharge `sur` (`cfPrice`). `CfOk` states, along
`constFpLoop`'s own recursion, that no expression rewrite raises its selected
cost and that each emitted re-assignment count is within the node's surcharge;
it is a property of the static compile-time rewrite, discharged per program.
Run equality and the constant-set invariant come from Flapjack's `cf_aux`. -/

theorem retCont_mono {C F : Type}
    (P Q : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (le : ∀ p s, P p s ≤ Q p s) (n : List Nat) (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (h : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat)) (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (rc : Option (WordSemResult 64)) (s2 : WordSemStateFiniteExact 64 C F) :
    retCont P n retCode l1 l2 h envs rc s2 ≤ retCont Q n retCode l1 l2 h envs rc s2 := by
  have mono := fun q t => wordExecutionCost_mono P Q le q t
  rcases rc with _ | (⟨x, ys⟩ | ⟨x, y⟩ | _ | _ | _ | _ | _ | _)
  all_goals try (exact Nat.le_refl 0)
  · simp only [retCont]
    split
    · exact Nat.le_refl 0
    · split
      · exact Nat.le_refl 0
      · split
        · exact mono _ _
        · exact Nat.le_refl 0
  · rcases h with _ | ⟨reg, hc, h1, h2⟩
    · exact Nat.le_refl 0
    · simp only [retCont]
      split
      · exact Nat.le_refl 0
      · split
        · exact mono _ _
        · exact Nat.le_refl 0

/-- A costlier price pays at least its own extra at a call node. -/
theorem wordExecutionCost_call_top {C F : Type}
    (P Q : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (le : ∀ p s, P p s ≤ Q p s) (ret : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (dest : Option Nat) (args : List Nat) (h : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost P (.call ret dest args h) s + (Q (.call ret dest args h) s - P (.call ret dest args h) s) ≤
      wordExecutionCost Q (.call ret dest args h) s := by
  have mono := fun q t => wordExecutionCost_mono P Q le q t
  have lp := le (.call ret dest args h) s
  rcases hg : WordSemStateFiniteExact.getVars args s with _ | xs
  · rw [wordExecutionCost, wordExecutionCost]; simp only [hg]; omega
  by_cases hbad : wordSemBadDestArgs dest args = true
  · rw [wordExecutionCost, wordExecutionCost]; simp only [hg, hbad, if_true]; omega
  have hbad' : wordSemBadDestArgs dest args = false := by simpa using hbad
  rcases hf : wordSemFindCode dest (wordSemAddRetLoc ret xs) s.code s.stackSize with _ | ⟨args1, prog, ss⟩
  · rw [wordExecutionCost, wordExecutionCost]
    simp only [hg, hbad', Bool.false_eq_true, if_false, hf]; omega
  rcases ret with _ | ⟨n, names, retCode, l1, l2⟩
  · rcases h with _ | hv
    · by_cases hz : s.clock = 0
      · rw [wordExecutionCost, wordExecutionCost]
        simp only [hg, hbad', Bool.false_eq_true, if_false, hf, hz, dite_true]; omega
      · simp only [wordSemAddRetLoc] at hf
        rw [tail_call_cost P dest args s xs hg hbad' args1 prog ss hf hz,
          tail_call_cost Q dest args s xs hg hbad' args1 prog ss hf hz]
        have := mono prog (callEnv args1 ss (decClock s))
        omega
    · rw [wordExecutionCost, wordExecutionCost]
      simp only [hg, hbad', Bool.false_eq_true, if_false, hf]; omega
  · simp only [wordSemAddRetLoc] at hf
    by_cases hdc : sptDomainEmpty names.1 ∨ ¬ n.Nodup
    · rw [wordExecutionCost, wordExecutionCost]
      simp only [hg, hbad', Bool.false_eq_true, if_false, wordSemAddRetLoc, hf, hdc, if_true]; omega
    rcases hce : wordSemCutEnvs names s.locals with _ | envs
    · rw [wordExecutionCost, wordExecutionCost]
      simp only [hg, hbad', Bool.false_eq_true, if_false, wordSemAddRetLoc, hf, hdc, hce]; omega
    by_cases hz : s.clock = 0
    · rw [wordExecutionCost, wordExecutionCost]
      simp only [hg, hbad', Bool.false_eq_true, if_false, wordSemAddRetLoc, hf, hdc, hce]
      simp only [hz, dite_true]; omega
    rcases hcv : evaluate prog (callEnv args1 ss (pushEnv envs h (decClock s))) with ⟨rc, s2⟩
    rw [ret_call_cost P n names retCode l1 l2 dest args h s xs hg hbad' args1 prog ss hf hdc envs hce hz rc s2 hcv,
      ret_call_cost Q n names retCode l1 l2 dest args h s xs hg hbad' args1 prog ss hf hdc envs hce hz rc s2 hcv]
    have := mono prog (callEnv args1 ss (pushEnv envs h (decClock s)))
    have := retCont_mono P Q le n retCode l1 l2 h envs rc s2
    omega

theorem shapePrice_preIsel {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) :
    ShapePrice (preIselPrice (C := C) (F := F) c) := by
  constructor
  all_goals try (intros; rfl)
  intro r d args x a a' l1 l2 s
  rcases r with _ | ⟨_, _, _, _, _⟩ <;> rfl

/-- Nodes that may carry a constant re-assignment surcharge. -/
def isSurNode : WordLangProgHOL (BitVec 64) → Bool
  | .call _ _ _ _ | .alloc _ _ | .ffi _ _ _ _ _ _ | .install _ _ _ _ _ => true
  | _ => false

/-- A node surcharge: only on calls/alloc/ffi/install, and blind to a call's
continuation and handler programs (so it survives their rewriting). -/
structure SurShape (e : WordLangProgHOL (BitVec 64) → Nat) : Prop where
  zero : ∀ p, isSurNode p = false → e p = 0
  callRet : ∀ v n a a' l1 l2 d args h,
    e (.call (some (v, n, a', l1, l2)) d args h) = e (.call (some (v, n, a, l1, l2)) d args h)
  callHandler : ∀ r d args x a a' l1 l2,
    e (.call r d args (some (x, a', l1, l2))) = e (.call r d args (some (x, a, l1, l2)))

theorem surShape_zero_fn : SurShape (fun _ => 0) := ⟨fun _ _ => rfl, fun _ _ _ _ _ _ _ _ _ => rfl,
  fun _ _ _ _ _ _ _ _ => rfl⟩

theorem surShape_add {e f : WordLangProgHOL (BitVec 64) → Nat} (he : SurShape e) (hf : SurShape f) :
    SurShape (fun p => e p + f p) :=
  ⟨fun p h => by simp [he.zero p h, hf.zero p h],
   fun v n a a' l1 l2 d args h => by simp only [he.callRet v n a a' l1 l2 d args h, hf.callRet v n a a' l1 l2 d args h],
   fun r d args x a a' l1 l2 => by simp only [he.callHandler r d args x a a' l1 l2, hf.callHandler r d args x a a' l1 l2]⟩

/-- Exact selector price plus 24 per surcharged constant re-assignment. -/
noncomputable def bP {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64)
    (e : WordLangProgHOL (BitVec 64) → Nat) (p : WordLangProgHOL (BitVec 64))
    (s : WordSemStateFiniteExact 64 C F) : Nat :=
  preIselPrice c p s + 24 * e p

theorem shapePrice_bP {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64)
    {e : WordLangProgHOL (BitVec 64) → Nat} (he : SurShape e) : ShapePrice (bP (C := C) (F := F) c e) := by
  have sp := shapePrice_preIsel (C := C) (F := F) c
  constructor
  · intro a b s; simp [bP, sp.seq0, he.zero (.seq a b) rfl]
  · intro s; simp [bP, sp.skip0, he.zero .skip rfl]
  · intro cmp r ri a b a' b' s
    simp [bP, sp.ite cmp r ri a b a' b' s, he.zero (.ite cmp r ri a b) rfl, he.zero (.ite cmp r ri a' b') rfl]
  · intro a a' s; simp [bP, sp.mustTerminate a a' s, he.zero (.mustTerminate a) rfl, he.zero (.mustTerminate a') rfl]
  · intro n a a' x s; simp [bP, sp.loop n a a' x s, he.zero (.loop n a x) rfl, he.zero (.loop n a' x) rfl]
  · intro v n a a' l1 l2 d args h s; simp only [bP, sp.callRet v n a a' l1 l2 d args h s, he.callRet v n a a' l1 l2 d args h]
  · intro r d args x a a' l1 l2 s
    simp only [bP, sp.callHandler r d args x a a' l1 l2 s, he.callHandler r d args x a a' l1 l2]

theorem smartSeq_cost_le {C F : Type} {P : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat}
    (sp : ShapePrice P) (a b : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost P (WordSimp.smartSeqHOL a b) s ≤ wordExecutionCost P (.seq a b) s := by
  cases a
  case skip =>
    simp only [WordSimp.smartSeqHOL]
    rw [wordExecutionCost_seq, sp.seq0, skip_cost sp, evaluate_skip_eq]
    dsimp only; omega
  all_goals exact Nat.le_refl _

/-- Number of constant re-assignments `dropConsts cs vs` emits. -/
def dropN (cs : Spt (BitVec 64)) (vs : List Nat) : Nat :=
  (vs.filter (fun n => (sptLookup n cs).isSome)).length

theorem iselX_assign_const (c : Compiler.Encoders.Asm.AsmConfigExact 64) (n : Nat) (w : BitVec 64) :
    iselX c (.assign n (.const w)) = 24 := by
  simp [iselX, WordInst.instSelectExecutable, WordInst.ExecutablePullExp.pullExpExecutable, WordInst.flattenExp,
    WordInst.instSelectExp, lineBound, isLeafProg, preAllocLeafBudget, WordToStack.refinedWordStackLeafBudget,
    WordToStack.refinedNativeInstructionPrice, Compiler.Encoders.Asm.HolInst.ofWordLangInst]

theorem dropConsts_cost {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64)
    {e : WordLangProgHOL (BitVec 64) → Nat} (he : SurShape e) (cs : Spt (BitVec 64)) :
    ∀ (vs : List Nat) (s : WordSemStateFiniteExact 64 C F), CsOk cs s →
      wordExecutionCost (bP c e) (dropConsts cs vs) s ≤ 24 * dropN cs vs := by
  intro vs
  induction vs with
  | nil => intro s _; simp only [dropConsts]; rw [wordCost_leaf _ rfl]; simp [bP, he.zero .skip rfl, preIselPrice,
      wordOptimizerLocalPrice, WordToStack.refinedWordLocalPrice, WordToStack.refinedWordStackLeafBudget]
  | cons n ns ih =>
    intro s hcs
    simp only [dropConsts, dropN, List.filter_cons]
    rcases hl : sptLookup n cs with _ | w
    · simp only [Option.isSome_none, Bool.false_eq_true, if_false]; exact ih s hcs
    · simp only [Option.isSome_some, if_true, List.length_cons]
      have sp := shapePrice_bP (C := C) (F := F) c he
      refine le_trans (smartSeq_cost_le sp _ _ s) ?_
      rw [wordExecutionCost_seq, sp.seq0, evaluate_drop_consts_1 cs ns 0 s hcs]
      dsimp only
      rw [wordCost_leaf (bP c e) (p := .assign n (.const w)) rfl]
      have h1 := ih s hcs
      have h2 : bP c e (.assign n (.const w)) s = 24 := by
        simp only [bP, he.zero (.assign n (.const w)) rfl]; exact iselX_assign_const c n w
      simp only [dropN] at h1
      omega

/-- What constant folding needs of a program, at constant set `cs`: no
expression rewrite raises its selected cost, and every constant re-assignment
emitted before a call/alloc/ffi/install is paid by that node's surcharge
`sur`. Mirrors `constFpLoop`'s recursion. -/
def CfOk (c : Compiler.Encoders.Asm.AsmConfigExact 64) (sur : WordLangProgHOL (BitVec 64) → Nat) :
    WordLangProgHOL (BitVec 64) → Spt (BitVec 64) → Prop
  | .assign v e, cs => iselX c (.assign v (constFpExp e cs)) ≤ iselX c (.assign v e)
  | .store e v, cs => iselX c (.store (constFpExp e cs) v) ≤ iselX c (.store e v)
  | .shareInst op v e, cs => iselX c (.shareInst op v (constFpExp e cs)) ≤ iselX c (.shareInst op v e)
  | .mustTerminate p, cs => CfOk c sur p cs
  | .seq p1 p2, cs => CfOk c sur p1 cs ∧ CfOk c sur p2 (constFpLoop p1 cs).2
  | .ite cmp lhs rhs p1 p2, cs =>
      match sptLookup lhs cs, getVarImmCs rhs cs with
      | some a, some b => if Compiler.Encoders.Asm.wordCmpHOL cmp a b then CfOk c sur p1 cs else CfOk c sur p2 cs
      | _, _ => CfOk c sur p1 cs ∧ CfOk c sur p2 cs
  | .call none dest args h, cs => dropN cs args ≤ sur (.call none dest args h)
  | .call (some (n, names, rh, l1, l2)) dest args none, cs =>
      dropN cs args ≤ sur (.call (some (n, names, rh, l1, l2)) dest args none) ∧
        CfOk c sur rh (deleteAll n (sptFilterV isGcConst (sptInter cs (allNames names))))
  | .call (some r) dest args (some h), cs => dropN cs args ≤ sur (.call (some r) dest args (some h))
  | .ffi x0 x1 x2 x3 x4 names, cs => dropN cs [x1, x2, x3, x4] ≤ sur (.ffi x0 x1 x2 x3 x4 names)
  | .alloc n names, cs => dropN cs [n] ≤ sur (.alloc n names)
  | .install r1 r2 r3 r4 names, cs => dropN cs [r1, r2, r3, r4] ≤ sur (.install r1 r2 r3 r4 names)
  | .loop _ body _, _ => CfOk c sur body .ln
  | _, _ => True

/-- Source price for constant folding: the exact selected-code price plus 24
per surcharged constant re-assignment. -/
noncomputable def cfPrice {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64)
    (e sur : WordLangProgHOL (BitVec 64) → Nat) (p : WordLangProgHOL (BitVec 64))
    (s : WordSemStateFiniteExact 64 C F) : Nat :=
  bP c (fun q => e q + sur q) p s

theorem drop_node_cost2 {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64)
    {e : WordLangProgHOL (BitVec 64) → Nat} (he : SurShape e)
    (sur : WordLangProgHOL (BitVec 64) → Nat) (cs : Spt (BitVec 64)) (vs : List Nat)
    (x y : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F) (hcs : CsOk cs s)
    (hd : dropN cs vs ≤ sur y)
    (top : wordExecutionCost (bP c e) x s + 24 * sur y ≤ wordExecutionCost (cfPrice c e sur) y s) :
    wordExecutionCost (bP c e) (WordSimp.smartSeqHOL (dropConsts cs vs) x) s ≤
      wordExecutionCost (cfPrice c e sur) y s := by
  have sp := shapePrice_bP (C := C) (F := F) c he
  refine le_trans (smartSeq_cost_le sp _ _ s) ?_
  rw [wordExecutionCost_seq, sp.seq0, evaluate_drop_consts_1 cs vs 0 s hcs]
  dsimp only
  have := dropConsts_cost c he cs vs s hcs
  omega

theorem preIsel_le_cf {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64)
    (e sur : WordLangProgHOL (BitVec 64) → Nat) (p : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F) :
    bP c e p s ≤ cfPrice c e sur p s := by simp only [cfPrice, bP]; omega

theorem cf_extra {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64)
    (e sur : WordLangProgHOL (BitVec 64) → Nat) (p : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F) :
    cfPrice c e sur p s = bP c e p s + 24 * sur p := by simp only [cfPrice, bP]; ring

theorem leaf_top {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64)
    (e sur : WordLangProgHOL (BitVec 64) → Nat) (x : WordLangProgHOL (BitVec 64)) (hx : isLeafProg x = true)
    (s : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost (bP c e) x s + 24 * sur x ≤ wordExecutionCost (cfPrice c e sur) x s := by
  rw [wordCost_leaf _ hx, wordCost_leaf _ hx, cf_extra]

theorem call_top {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64)
    (e sur : WordLangProgHOL (BitVec 64) → Nat) ret dest args h (s : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost (bP c e) (.call ret dest args h) s + 24 * sur (.call ret dest args h) ≤
      wordExecutionCost (cfPrice c e sur) (.call ret dest args h) s := by
  have := wordExecutionCost_call_top (bP c e) (cfPrice c e sur) (preIsel_le_cf c e sur) ret dest args h s
  rw [cf_extra, Nat.add_sub_cancel_left] at this
  exact this

/-- Two-price loop congruence: a body with the same runs and no more work
(at the respective prices) gives a loop with no more work. -/
theorem loop_cost2 {C F : Type} (P Q : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (names exits : WordLangNumSetHOL) (body body' : WordLangProgHOL (BitVec 64))
    (hpl : ∀ s, P (.loop names body' exits) s ≤ Q (.loop names body exits) s)
    (hbE : ∀ s : WordSemStateFiniteExact 64 C F, gcFunConstOk s.gcFun → evaluate body' s = evaluate body s)
    (hbC : ∀ s : WordSemStateFiniteExact 64 C F, gcFunConstOk s.gcFun → (evaluate body s).1 ≠ some .error →
      wordExecutionCost P body' s ≤ wordExecutionCost Q body s) :
    ∀ (n : Nat) (s : WordSemStateFiniteExact 64 C F), s.clock = n → gcFunConstOk s.gcFun →
      (evaluate (.loop names body exits) s).1 ≠ some .error →
      wordExecutionCost P (.loop names body' exits) s ≤ wordExecutionCost Q (.loop names body exits) s := by
  have ht := (evaluate_def_rebound (width := 64) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro s hn g ok
  have hp := hpl s
  rcases hcs : cutState (names, .ln) s with _ | cs
  · rw [loop_cost_cut_none P names body' exits s hcs, loop_cost_cut_none Q names body exits s hcs]; exact hp
  have gcs : gcFunConstOk cs.gcFun := by
    obtain ⟨l, rfl⟩ := cutStateConst _ _ _ hcs; exact g
  rcases hbr : evaluate body cs with ⟨r1, s1⟩
  have hbT : evaluate body' cs = (r1, s1) := (hbE cs gcs).trans hbr
  rw [ht, hcs] at ok
  dsimp only at ok
  rw [hbr] at ok
  dsimp only at ok
  have okb : (evaluate body cs).1 ≠ some .error := by
    rw [hbr]; rintro rfl
    simp [wordSemContLoop, wordSemExitLoop] at ok
  have kb := hbC cs gcs okb
  rw [loop_cost_clause Q names body exits s cs hcs r1 s1 hbr, loop_cost_clause P names body' exits s cs hcs r1 s1 hbT]
  by_cases hcont : wordSemContLoop r1 = true
  · simp only [hcont, if_true] at ok ⊢
    by_cases hz : s1.clock = 0
    · simp only [hz, if_true]; omega
    · simp only [hz, if_false, wordSemSTOP] at ok ⊢
      have hlt : (decClock s1).clock < n := by
        have := Flapjack.WordAlloc.loopBodyRecursiveClockLt (names, .ln) body s cs s1 r1 hcs hbr hz
        omega
      have g1 : gcFunConstOk (decClock s1).gcFun := evaluate_gc_fun_const_ok body cs r1 s1 ⟨hbr, gcs⟩
      have := ih _ hlt (decClock s1) rfl g1 ok
      omega
  · simp only [hcont, Bool.false_eq_true, if_false]; omega

/-- Constant folding's cost transfer. -/
theorem cf_cost {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64)
    {bg : WordLangProgHOL (BitVec 64) → Nat} (he : SurShape bg) (sur : WordLangProgHOL (BitVec 64) → Nat) :
    ∀ (p : WordLangProgHOL (BitVec 64)) (cs : Spt (BitVec 64)) (s : WordSemStateFiniteExact 64 C F),
      gcFunConstOk s.gcFun → CsOk cs s → CfOk c sur p cs → (evaluate p s).1 ≠ some .error →
      wordExecutionCost (bP c bg) (constFpLoop p cs).1 s ≤ wordExecutionCost (cfPrice c bg sur) p s
  | .assign v e, cs, s, _, _, hok, _ => by
      have : (constFpLoop (.assign v e) cs).1 = .assign v (constFpExp e cs) := by
        simp only [constFpLoop]; split <;> rfl
      rw [this, wordCost_leaf _ rfl, wordCost_leaf _ rfl, cf_extra]
      simp only [CfOk] at hok
      simp only [bP, preIselPrice, he.zero (.assign v (constFpExp e cs)) rfl, he.zero (.assign v e) rfl]; omega
  | .store e v, cs, s, _, _, hok, _ => by
      simp only [constFpLoop]
      rw [wordCost_leaf _ rfl, wordCost_leaf _ rfl, cf_extra]
      simp only [CfOk] at hok
      simp only [bP, preIselPrice, he.zero (.store (constFpExp e cs) v) rfl, he.zero (.store e v) rfl]; omega
  | .shareInst op v e, cs, s, _, _, hok, _ => by
      have : (constFpLoop (.shareInst op v e) cs).1 = .shareInst op v (constFpExp e cs) := by
        cases op <;> simp only [constFpLoop]
      rw [this, wordCost_leaf _ rfl, wordCost_leaf _ rfl, cf_extra]
      simp only [CfOk] at hok
      simp only [bP, preIselPrice, he.zero (.shareInst op v (constFpExp e cs)) rfl, he.zero (.shareInst op v e) rfl]
      omega
  | .alloc n names, cs, s, _, hcs, hok, _ => by
      simp only [constFpLoop]
      exact drop_node_cost2 c he sur cs _ _ _ s hcs hok (leaf_top c bg sur _ rfl s)
  | .ffi x0 x1 x2 x3 x4 names, cs, s, _, hcs, hok, _ => by
      simp only [constFpLoop]
      exact drop_node_cost2 c he sur cs _ _ _ s hcs hok (leaf_top c bg sur _ rfl s)
  | .install r1 r2 r3 r4 names, cs, s, _, hcs, hok, _ => by
      simp only [constFpLoop]
      exact drop_node_cost2 c he sur cs _ _ _ s hcs hok (leaf_top c bg sur _ rfl s)
  | .call none dest args h, cs, s, _, hcs, hok, _ => by
      simp only [constFpLoop]
      exact drop_node_cost2 c he sur cs _ _ _ s hcs hok (call_top c bg sur _ _ _ _ s)
  | .call (some r) dest args (some h), cs, s, _, hcs, hok, _ => by
      simp only [constFpLoop]
      exact drop_node_cost2 c he sur cs _ _ _ s hcs hok (call_top c bg sur _ _ _ _ s)
  | .call (some (n, names, rh, l1, l2)) dest args none, cs, s, hok0, hcs, hok, ok => by
      have ht := (evaluate_def_rebound (width := 64) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
      have sp := shapePrice_bP (C := C) (F := F) c he
      simp only [CfOk] at hok
      simp only [constFpLoop]
      rcases hr : constFpLoop rh (deleteAll n (sptFilterV isGcConst (sptInter cs (allNames names)))) with ⟨rh', cs''⟩
      dsimp only
      refine drop_node_cost2 c he sur cs args _ _ s hcs hok.1 ?_
      have pXY := sp.callRet n names rh rh' l1 l2 dest args none s
      have qY := cf_extra c bg sur (.call (some (n, names, rh, l1, l2)) dest args none) s
      rw [ht] at ok
      rcases hgv : WordSemStateFiniteExact.getVars args s with _ | xs
      · simp only [hgv] at ok; exact absurd rfl ok
      simp only [hgv] at ok
      by_cases hbad : wordSemBadDestArgs dest args = true
      · simp only [hbad, if_true] at ok; exact absurd rfl ok
      have hbad' : wordSemBadDestArgs dest args = false := by simpa using hbad
      simp only [hbad', Bool.false_eq_true, if_false, wordSemAddRetLoc] at ok
      rcases hf : wordSemFindCode dest (.loc l1 l2 :: xs) s.code s.stackSize with _ | ⟨args1, prog, ss⟩
      · simp only [hf] at ok; exact absurd rfl ok
      simp only [hf] at ok
      by_cases hdc : sptDomainEmpty names.1 ∨ ¬ n.Nodup
      · simp only [hdc, if_true] at ok; exact absurd rfl ok
      simp only [hdc, if_false] at ok
      rcases hce : wordSemCutEnvs names s.locals with _ | envs
      · simp only [hce] at ok; exact absurd rfl ok
      simp only [hce] at ok
      by_cases hz : s.clock = 0
      · rw [wordExecutionCost, wordExecutionCost]
        simp only [hgv, hbad', Bool.false_eq_true, if_false, wordSemAddRetLoc, hf, hdc, hce]
        simp only [hz, dite_true]
        omega
      simp only [hz, if_false] at ok
      rcases hcv : evaluate prog (callEnv args1 ss (pushEnv envs none (decClock s))) with ⟨rc, s2⟩
      rw [hcv] at ok
      rw [ret_call_cost (bP c bg) n names rh' l1 l2 dest args none s xs hgv hbad' args1 prog ss hf hdc envs
          hce hz rc s2 hcv,
        ret_call_cost (cfPrice c bg sur) n names rh l1 l2 dest args none s xs hgv hbad' args1 prog ss hf hdc envs
          hce hz rc s2 hcv]
      have mb := wordExecutionCost_mono (bP c bg) (cfPrice c bg sur) (preIsel_le_cf c bg sur) prog
        (callEnv args1 ss (pushEnv envs none (decClock s)))
      suffices kr : retCont (bP c bg) n rh' l1 l2 none envs rc s2 ≤
          retCont (cfPrice c bg sur) n rh l1 l2 none envs rc s2 by omega
      rcases rc with _ | (⟨x, ys⟩ | ⟨x, y⟩ | _ | _ | _ | _ | _ | _)
      all_goals try (exact Nat.le_refl 0)
      simp only at ok
      simp only [retCont]
      by_cases hx : x ≠ WordLocW.loc l1 l2 ∨ ys.length ≠ n.length
      · simp only [hx, if_true]; exact Nat.le_refl 0
      simp only [hx, if_false] at ok ⊢
      rcases hp : popEnv s2 with _ | s1
      · exact Nat.le_refl 0
      simp only [hp] at ok
      by_cases hdom : sptDomainEqUnion s1.locals envs.1 envs.2
      · simp only [hdom, if_true] at ok ⊢
        have hgf : (callEnv args1 ss (pushEnv envs none (decClock s))).gcFun = s.gcFun := rfl
        have hok2 : gcFunConstOk s2.gcFun := by
          rw [← (evaluate_consts prog _ _ s2 hcv).1, hgf]; exact hok0
        have hok1 : gcFunConstOk (setVars n ys s1).gcFun := pop_env_gc_fun_const_ok s2 s1 ⟨hp, hok2⟩
        have hsf := evaluate_sf_gc_consts prog _ s2 _ ⟨hcv, by rw [hgf]; exact hok0⟩
        simp only [sfMotive] at hsf
        have hcs' : CsOk (deleteAll n (sptFilterV isGcConst (sptInter cs (allNames names))))
            (setVars n ys s1) := by
          intro v w hv
          obtain ⟨hv1, hvn⟩ := lookup_FOLDR_delete n _ v w hv
          have hgc := lookup_filter_v_SOME _ v w _ hv1
          have hv2 := lookup_filter_v_SOME_imp _ v w _ hv1
          rw [sptLookup_sptInterCases] at hv2
          rcases h1 : sptLookup v cs with _ | cc <;>
            rcases h2 : sptLookup v (allNames names) with _ | u <;>
            simp only [h1, h2, reduceCtorEq] at hv2
          simp only [Option.some.injEq] at hv2; subst hv2
          rw [get_var_set_vars_ignore v n ys s1 hvn]
          exact push_env_pop_env_locals_thm (decClock s) _ s2 s1 envs names none
            ⟨hce, rfl, hsf.1, hp⟩ v (.word cc) ⟨hcs v cc h1, hgc, by rw [h2]; simp⟩
        have ih := cf_cost c he sur rh _ (setVars n ys s1) hok1 hcs' hok.2 ok
        rw [hr] at ih
        exact ih
      · simp only [hdom]; exact Nat.le_refl 0
  | .seq p1 p2, cs, s, hg, hcs, hok, ok => by
      have aux1 := cf_aux (width := 64) p1 cs s hg hcs
      simp only [CfOk] at hok
      have ih1 := cf_cost c he sur p1 cs s hg hcs hok.1 (seq_ok_left ok)
      simp only [constFpLoop]
      rcases h1 : constFpLoop p1 cs with ⟨p1', cs1⟩
      rw [h1] at aux1 ih1 hok
      simp only [CfGoal] at aux1 ih1 hok
      rcases h2 : constFpLoop p2 cs1 with ⟨p2', cs2⟩
      dsimp only
      rw [wordExecutionCost_seq, wordExecutionCost_seq, (shapePrice_bP c he).seq0, aux1.1]
      rcases hev1 : evaluate p1 s with ⟨_ | r, s1⟩
      · have g1 : gcFunConstOk s1.gcFun := evaluate_gc_fun_const_ok p1 s none s1 ⟨hev1, hg⟩
        rw [hev1] at aux1
        have ih2 := cf_cost c he sur p2 cs1 s1 g1 (aux1.2 rfl) hok.2 (seq_ok_right ok hev1)
        rw [h2] at ih2
        dsimp only at ih2 ⊢
        omega
      · dsimp only; omega
  | .mustTerminate q, cs, s, hg, hcs, hok, ok => by
      have ht := (evaluate_def_rebound (width := 64) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
      simp only [CfOk] at hok
      simp only [constFpLoop]
      rcases hq : constFpLoop q cs with ⟨q', cs1⟩
      dsimp only
      rw [wordExecutionCost, wordExecutionCost]
      have pr : bP c bg (.mustTerminate q') s ≤ cfPrice c bg sur (.mustTerminate q) s := by
        rw [cf_extra, (shapePrice_bP c he).mustTerminate q q' s]; omega
      by_cases hz : s.termdep = 0
      · simp only [hz, dite_true]; omega
      simp only [hz, dite_false]
      rw [ht] at ok
      simp only [hz, if_false] at ok
      generalize hL : wordSemMustTerminateLimit 64 = L at ok ⊢
      have okb : (evaluate q { s with clock := L, termdep := s.termdep - 1 }).1 ≠ some .error := by
        rcases hb : evaluate q { s with clock := L, termdep := s.termdep - 1 } with ⟨r, s1⟩
        rw [hb] at ok
        rintro rfl; simp at ok
      have ih := cf_cost c he sur q cs { s with clock := L, termdep := s.termdep - 1 } hg
        (csOk_same_locals hcs rfl) hok okb
      rw [hq] at ih
      dsimp only at ih
      omega
  | .ite cmp lhs rhs p1 p2, cs, s, hg, hcs, hok, ok => by
      have ht := (evaluate_def_rebound (width := 64) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have pr : ∀ a b, bP c bg (.ite cmp lhs rhs a b) s ≤ cfPrice c bg sur (.ite cmp lhs rhs p1 p2) s := by
        intro a b; rw [cf_extra, (shapePrice_bP c he).ite cmp lhs rhs p1 p2 a b s]; omega
      have ih1 := fun (h1 : CfOk c sur p1 cs) (okb : (evaluate p1 s).1 ≠ some .error) =>
        cf_cost c he sur p1 cs s hg hcs h1 okb
      have ih2 := fun (h2 : CfOk c sur p2 cs) (okb : (evaluate p2 s).1 ≠ some .error) =>
        cf_cost c he sur p2 cs s hg hcs h2 okb
      simp only [CfOk] at hok
      simp only [constFpLoop]
      rw [ht] at ok
      rcases hl : sptLookup lhs cs with _ | clhs <;> rcases hr : getVarImmCs rhs cs with _ | crhs
      rotate_left 3
      · -- decided statically
        rw [hl, hr] at hok
        dsimp only at hok ⊢
        have hgv : getVar lhs s = some (.word clhs) := hcs lhs clhs hl
        have hgi := get_var_imm_cs_imp_get_var_imm rhs crhs s cs ⟨hcs, hr⟩
        rw [hgv, hgi] at ok
        simp only [wordSemWordCmp] at ok
        conv_rhs => rw [wordExecutionCost]
        rw [hgv, hgi]
        simp only [wordSemWordCmp]
        split_ifs at hok ok ⊢ with hc
        · simp only [hc] at ok ⊢
          have := ih1 hok ok; omega
        · simp only [Bool.not_eq_true] at hc
          simp only [hc] at ok ⊢
          have := ih2 hok ok; omega
      all_goals
        simp only [hl, hr] at hok
        rcases h1 : constFpLoop p1 cs with ⟨p1', cs1⟩
        rcases h2 : constFpLoop p2 cs with ⟨p2', cs2⟩
        dsimp only
        rw [wordExecutionCost, wordExecutionCost]
        have e1 := ih1 hok.1; have e2 := ih2 hok.2
        rw [h1] at e1; rw [h2] at e2
        dsimp only at e1 e2
        have pr' := pr p1' p2'
        rcases hx : getVar lhs s with _ | x
        · simp only; omega
        rcases hy : getVarImm rhs s with _ | y
        · simp only; omega
        rw [hx, hy] at ok
        dsimp only at ok ⊢
        rcases hc : wordSemWordCmp cmp x y with _ | _ | _
        · simp only; omega
        · rw [hc] at ok; have := e2 ok; dsimp only; omega
        · rw [hc] at ok; have := e1 ok; dsimp only; omega
  | .loop names body exits, cs, s, hg, hcs, hok, ok => by
      simp only [CfOk] at hok
      simp only [constFpLoop]
      exact loop_cost2 (bP c bg) (cfPrice c bg sur) names exits body _
        (fun s => by rw [cf_extra, (shapePrice_bP c he).loop names body _ exits s]; omega)
        (fun v gv => (cf_aux (width := 64) body .ln v gv (csOk_ln v)).1)
        (fun v gv okv => cf_cost c he sur body .ln v gv (csOk_ln v) hok okv) s.clock s rfl hg ok
  | .move a b, cs, s, _, _, _, _ | .inst a, cs, s, _, _, _, _ | .get a b, cs, s, _, _, _, _
  | .opCurrHeap a b d, cs, s, _, _, _, _ | .locValue a b, cs, s, _, _, _, _
  | .storeConsts a b d e f, cs, s, _, _, _, _ | .skip, cs, s, _, _, _, _ | .set a b, cs, s, _, _, _, _
  | .tick, cs, s, _, _, _, _ | .raise a, cs, s, _, _, _, _ | .return a b, cs, s, _, _, _, _
  | .break a, cs, s, _, _, _, _ | .continue a, cs, s, _, _, _, _
  | .codeBufferWrite a b, cs, s, _, _, _, _ | .dataBufferWrite a b, cs, s, _, _, _, _ => by
      simp only [constFpLoop]
      exact wordExecutionCost_mono _ _ (preIsel_le_cf c bg sur) _ s

/-- Constant folding endpoint: same run from every gc-safe state, and the
folded program's work at the exact selector price is at most the source's at
the price plus its constant re-assignment surcharge. -/
theorem constFp_run_cost {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64)
    {e : WordLangProgHOL (BitVec 64) → Nat} (he : SurShape e)
    (sur : WordLangProgHOL (BitVec 64) → Nat) (p : WordLangProgHOL (BitVec 64)) (hok : CfOk c sur p .ln)
    (s : WordSemStateFiniteExact 64 C F) (g : gcFunConstOk s.gcFun) (ok : (evaluate p s).1 ≠ some .error) :
    evaluate (constFp p) s = evaluate p s ∧
      wordExecutionCost (bP c e) (constFp p) s ≤ wordExecutionCost (cfPrice c e sur) p s :=
  ⟨evaluate_const_fp p s g, cf_cost c he sur p .ln s g (csOk_ln s) hok ok⟩

#print axioms constFp_run_cost
#print axioms cf_cost
#print axioms wordExecutionCost_call_top
end InitECandidate.Runtime.FineCost
