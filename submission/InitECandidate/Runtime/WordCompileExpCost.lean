import InitECandidate.Runtime.WordConstFpCost
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact Flapjack.Compiler.Backend.WordSimp

/-! Cost transfer for `simpDuplicateIf` and the whole WordSimp `compileExp`.
A successful if-hoist turns `ite; interm; p2` into a constant-folded `ite`
with `interm; p2` in both branches: the restructuring costs no more on every
path (`hoist_ite_cost`), and the re-applied constant folding is paid by a hoist
surcharge (`HoistOk2`/`CfOk`). Hoists nested inside are paid by the remaining
budget, at the raised background price (`SdiOk`). Two-price congruences
(`Le2`) carry the recursion. `compileExp_run_cost` composes seqAssoc, constFp,
simpDuplicateIf and pushOutIf into one run+cost endpoint at the exact selector
price. -/

variable {C F : Type}

theorem wordExecutionCost_ite (P : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (cmp : Cmp) (lhs : Nat) (rhs : WordRegImm (BitVec 64)) (a b : WordLangProgHOL (BitVec 64))
    (s : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost P (.ite cmp lhs rhs a b) s = P (.ite cmp lhs rhs a b) s +
      match getVar lhs s, getVarImm rhs s with
      | some x, some y => match wordSemWordCmp cmp x y with
        | some true => wordExecutionCost P a s
        | some false => wordExecutionCost P b s
        | none => 0
      | _, _ => 0 := by
  rw [wordExecutionCost]
  rcases getVar lhs s with _ | x <;> rcases getVarImm rhs s with _ | y <;> simp only
  rcases wordSemWordCmp cmp x y with _ | _ | _ <;> rfl

section TwoPrice
variable (P Q : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)

/-- `q'` runs as `q` from gc-safe states and costs at `P` at most `q` at `Q`. -/
def Le2 (q q' : WordLangProgHOL (BitVec 64)) : Prop :=
  (∀ s : WordSemStateFiniteExact 64 C F, gcFunConstOk s.gcFun → evaluate q' s = evaluate q s) ∧
  (∀ s : WordSemStateFiniteExact 64 C F, gcFunConstOk s.gcFun → (evaluate q s).1 ≠ some .error →
    wordExecutionCost P q' s ≤ wordExecutionCost Q q s)

theorem le2_seq (spP : ShapePrice P) {a a' b b' : WordLangProgHOL (BitVec 64)}
    (ha : Le2 P Q a a') (hb : Le2 P Q b b') : Le2 P Q (.seq a b) (.seq a' b') := by
  refine ⟨fun s g => evaluate_seq_congr_gc s g (ha.1 s g) hb.1, fun s g ok => ?_⟩
  have ca := ha.2 s g (seq_ok_left ok)
  rw [wordExecutionCost_seq, wordExecutionCost_seq (price := Q), spP.seq0, ha.1 s g]
  rcases h : evaluate a s with ⟨_ | r, s1⟩
  · have g1 : gcFunConstOk s1.gcFun := evaluate_gc_fun_const_ok a s none s1 ⟨h, g⟩
    have cb := hb.2 s1 g1 (seq_ok_right ok h)
    dsimp only; omega
  · dsimp only; omega

theorem le2_ite (cmp : Cmp) (r : Nat) (ri : WordRegImm (BitVec 64))
    {a a' b b' : WordLangProgHOL (BitVec 64)}
    (hpr : ∀ s, P (.ite cmp r ri a' b') s ≤ Q (.ite cmp r ri a b) s)
    (ha : Le2 P Q a a') (hb : Le2 P Q b b') : Le2 P Q (.ite cmp r ri a b) (.ite cmp r ri a' b') := by
  have ht := (evaluate_def_rebound (width := 64) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨evaluate_ite_congr_gc cmp r ri ha.1 hb.1, fun s g ok => ?_⟩
  rw [ht] at ok
  rw [wordExecutionCost_ite, wordExecutionCost_ite]
  have := hpr s
  rcases hx : getVar r s with _ | x
  · simp only; omega
  rcases hy : getVarImm ri s with _ | y
  · simp only; omega
  rw [hx, hy] at ok
  dsimp only at ok ⊢
  rcases hc : wordSemWordCmp cmp x y with _ | _ | _
  · simp only; omega
  · rw [hc] at ok; have := hb.2 s g ok; dsimp only; omega
  · rw [hc] at ok; have := ha.2 s g ok; dsimp only; omega

theorem le2_mustTerminate {a a' : WordLangProgHOL (BitVec 64)}
    (hpr : ∀ s, P (.mustTerminate a') s ≤ Q (.mustTerminate a) s) (ha : Le2 P Q a a') :
    Le2 P Q (.mustTerminate a) (.mustTerminate a') := by
  have ht := (evaluate_def_rebound (width := 64) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨evaluate_mustTerminate_congr_gc ha.1, fun s g ok => ?_⟩
  rw [ht] at ok
  rw [wordExecutionCost, wordExecutionCost]
  have := hpr s
  by_cases hz : s.termdep = 0
  · simp only [hz, dite_true]; omega
  simp only [hz, if_false, dite_false] at ok ⊢
  generalize hL : wordSemMustTerminateLimit 64 = L at ok ⊢
  have okb : (evaluate a { s with clock := L, termdep := s.termdep - 1 }).1 ≠ some .error := by
    rcases hb : evaluate a { s with clock := L, termdep := s.termdep - 1 } with ⟨r, s1⟩
    rw [hb] at ok
    rintro rfl; simp at ok
  have := ha.2 { s with clock := L, termdep := s.termdep - 1 } g okb
  omega

theorem le2_callSome (hpq : ∀ p s, P p s ≤ Q p s) (v : List Nat) (names : WordLangCutsetsHOL)
    {k k' : WordLangProgHOL (BitVec 64)} (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    {h h' : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat)}
    (hpr : ∀ x, P (.call (some (v, names, k', l1, l2)) dest args h') x ≤ Q (.call (some (v, names, k, l1, l2)) dest args h) x)
    (hk : Le2 P Q k k')
    (hh : (h = none ∧ h' = none) ∨ ∃ x hp hp' a b, h = some (x, hp, a, b) ∧ h' = some (x, hp', a, b) ∧
      Le2 P Q hp hp') :
    Le2 P Q (.call (some (v, names, k, l1, l2)) dest args h) (.call (some (v, names, k', l1, l2)) dest args h') := by
  have ht := (evaluate_def_rebound (width := 64) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hpush : ∀ (envs : Spt (WordLocW 64) × Spt (WordLocW 64)) (x : WordSemStateFiniteExact 64 C F),
      pushEnv envs h' x = pushEnv envs h x := by
    rcases hh with ⟨rfl, rfl⟩ | ⟨x, hp, hp', a, b, rfl, rfl, -⟩ <;> intros <;> rfl
  constructor
  · intro s g
    have e1 := evalEq_call_ret_gc (fun w gw => (hk.1 w gw).symm) v names l1 l2 dest args h s g
    rw [e1]
    rcases hh with ⟨rfl, rfl⟩ | ⟨y, hp, hp', a, b, rfl, rfl, hph⟩
    · rfl
    · exact (evalEq_call_handler_gc (fun w gw => (hph.1 w gw).symm) _ dest args y a b s g).symm
  intro s g ok
  have hp0 := hpr s
  rw [ht] at ok
  rcases hg : WordSemStateFiniteExact.getVars args s with _ | xs
  · simp only [hg] at ok; exact absurd rfl ok
  simp only [hg] at ok
  by_cases hbad : wordSemBadDestArgs dest args = true
  · simp only [hbad, if_true] at ok; exact absurd rfl ok
  have hbad' : wordSemBadDestArgs dest args = false := by simpa using hbad
  simp only [hbad', Bool.false_eq_true, if_false, wordSemAddRetLoc] at ok
  rcases hf : wordSemFindCode dest (.loc l1 l2 :: xs) s.code s.stackSize with _ | ⟨args1, prog, ss⟩
  · simp only [hf] at ok; exact absurd rfl ok
  simp only [hf] at ok
  by_cases hdc : sptDomainEmpty names.1 ∨ ¬ v.Nodup
  · simp only [hdc, if_true] at ok; exact absurd rfl ok
  simp only [hdc, if_false] at ok
  rcases hce : wordSemCutEnvs names s.locals with _ | envs
  · simp only [hce] at ok; exact absurd rfl ok
  simp only [hce] at ok
  by_cases hz : s.clock = 0
  · rw [wordExecutionCost, wordExecutionCost]
    simp only [hg, hbad', Bool.false_eq_true, if_false, wordSemAddRetLoc, hf, hdc, hce]
    simp only [hz, dite_true]
    exact hp0
  simp only [hz, if_false] at ok
  rcases hcv : evaluate prog (callEnv args1 ss (pushEnv envs h (decClock s))) with ⟨rc, s2⟩
  rw [hcv] at ok
  have hcvT : evaluate prog (callEnv args1 ss (pushEnv envs h' (decClock s))) = (rc, s2) := by
    rw [hpush]; exact hcv
  have g2 : gcFunConstOk s2.gcFun := by
    rw [← (evaluate_consts prog _ _ s2 hcv).1, gcFun_callEnv_pushEnv]; exact g
  rw [ret_call_cost P v names k' l1 l2 dest args h' s xs hg hbad' args1 prog ss hf hdc envs hce hz rc s2 hcvT,
    ret_call_cost Q v names k l1 l2 dest args h s xs hg hbad' args1 prog ss hf hdc envs hce hz rc s2 hcv, hpush]
  have mb := wordExecutionCost_mono P Q hpq prog (callEnv args1 ss (pushEnv envs h (decClock s)))
  suffices kr : retCont P v k' l1 l2 h' envs rc s2 ≤ retCont Q v k l1 l2 h envs rc s2 by omega
  rcases rc with _ | (⟨x, ys⟩ | ⟨x, y⟩ | _ | _ | _ | _ | _ | _)
  all_goals try (exact Nat.le_refl 0)
  · simp only at ok
    simp only [retCont]
    by_cases hx : x ≠ WordLocW.loc l1 l2 ∨ ys.length ≠ v.length
    · simp only [hx, if_true]; exact Nat.le_refl 0
    simp only [hx, if_false] at ok ⊢
    rcases hp : popEnv s2 with _ | s1
    · exact Nat.le_refl 0
    simp only [hp] at ok
    by_cases hdom : sptDomainEqUnion s1.locals envs.1 envs.2
    · simp only [hdom, if_true] at ok ⊢
      exact hk.2 _ (pop_env_gc_fun_const_ok s2 s1 ⟨hp, g2⟩) ok
    · simp only [hdom]; exact Nat.le_refl 0
  · rcases hh with ⟨rfl, rfl⟩ | ⟨y', hp, hp', a, b, rfl, rfl, hph⟩
    · simp only [retCont]; exact Nat.le_refl 0
    simp only at ok
    simp only [retCont]
    by_cases hx : x ≠ WordLocW.loc a b
    · rw [if_pos hx, if_pos hx]
    rw [if_neg hx, if_neg hx]
    rw [if_neg hx] at ok
    by_cases hdom : sptDomainEqUnion s2.locals envs.1 envs.2
    · simp only [hdom, if_true] at ok ⊢
      exact hph.2 _ g2 ok
    · simp only [hdom]; exact Nat.le_refl 0

/-- A call with no return continuation never runs its handler program. -/
theorem le2_callNoneHandler (dest : Option Nat) (args : List Nat) (x : Nat)
    {hp hp' : WordLangProgHOL (BitVec 64)} (a b : Nat)
    (hpr : ∀ s, P (.call none dest args (some (x, hp', a, b))) s ≤ Q (.call none dest args (some (x, hp, a, b))) s)
    (hph : ∀ s : WordSemStateFiniteExact 64 C F, gcFunConstOk s.gcFun → evaluate hp' s = evaluate hp s) :
    Le2 P Q (.call none dest args (some (x, hp, a, b))) (.call none dest args (some (x, hp', a, b))) := by
  refine ⟨fun s g => (evalEq_call_handler_gc (fun w gw => (hph w gw).symm) none dest args x a b s g).symm,
    fun s g ok => ?_⟩
  rw [wordExecutionCost, wordExecutionCost]
  have hE := hpr s
  rcases hgv : WordSemStateFiniteExact.getVars args s with _ | xs
  · simp only; exact hE
  simp only
  by_cases hbad : wordSemBadDestArgs dest args = true
  · simp only [hbad, if_true]; exact hE
  simp only [hbad, Bool.false_eq_true, if_false, wordSemAddRetLoc]
  rcases hf : wordSemFindCode dest xs s.code s.stackSize with _ | ⟨args1, prog, ss⟩
  all_goals simp only; exact hE

end TwoPrice

/-- Hoisting `I; X` into both branches costs no more than running it after the `ite`. -/
theorem hoist_ite_cost {P : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat}
    (sp : ShapePrice P) (cmp : Cmp) (lhs : Nat) (rhs : WordRegImm (BitVec 64))
    (br1 br2 I X : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost P (.ite cmp lhs rhs (.seq (.seq br1 I) X) (.seq (.seq br2 I) X)) s ≤
      wordExecutionCost P (.seq (.seq (.ite cmp lhs rhs br1 br2) I) X) s := by
  have ht := (evaluate_def_rebound (width := 64) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [wordExecutionCost_seq, wordExecutionCost_seq, sp.seq0, sp.seq0, evaluate_seq_eq, ht]
  rw [wordExecutionCost_ite, wordExecutionCost_ite, sp.ite cmp lhs rhs br1 br2 _ _ s]
  rcases hx : getVar lhs s with _ | x
  · simp
  rcases hy : getVarImm rhs s with _ | y
  · simp
  dsimp only
  rcases hc : wordSemWordCmp cmp x y with _ | _ | b
  · simp
  all_goals
    dsimp only
    rw [wordExecutionCost_seq, wordExecutionCost_seq, sp.seq0, sp.seq0, evaluate_seq_eq]
    rcases h1 : evaluate _ s with ⟨_ | r, s1⟩
    · dsimp only
      rcases h2 : evaluate I s1 with ⟨_ | r2, s2⟩ <;> dsimp only <;> omega
    · dsimp only; omega

/-- What a successful `tryIfHoist2` needs: its constant folding of the hoisted
`ite` is paid by the hoist surcharge `h`. Mirrors `tryIfHoist2`. -/
def HoistOk2 (c : Compiler.Encoders.Asm.AsmConfigExact 64) (h : WordLangProgHOL (BitVec 64) → Nat) :
    Nat → WordLangProgHOL (BitVec 64) → WordLangProgHOL (BitVec 64) → WordLangProgHOL (BitVec 64) →
      WordLangProgHOL (BitVec 64) → Prop
  | 0, _, _, _, _ => True
  | n + 1, p1, interm, dummy, p2 =>
      match p1 with
      | .ite cmp lhs rhs br1 br2 =>
          CfOk c h (.ite cmp lhs rhs (.seq (.seq br1 interm) p2) (.seq (.seq br2 interm) p2)) .ln
      | .seq p3 p4 =>
          match destIf p4 with
          | some (cmp, lhs, rhs, br1, br2) =>
              CfOk c h (.ite cmp lhs rhs (.seq (.seq br1 interm) p2) (.seq (.seq br2 interm) p2)) .ln
          | none => HoistOk2 c h n p3 (.seq p4 interm) dummy p2
      | _ => True

/-- The hoisted, re-folded `ite` costs no more than the original sequence. -/
theorem hoisted_cost (c : Compiler.Encoders.Asm.AsmConfigExact 64) {bg h : WordLangProgHOL (BitVec 64) → Nat}
    (hbg : SurShape bg) (hh : SurShape h) (cmp : Cmp) (lhs : Nat) (rhs : WordRegImm (BitVec 64))
    (br1 br2 I X : WordLangProgHOL (BitVec 64))
    (hok : CfOk c h (.ite cmp lhs rhs (.seq (.seq br1 I) X) (.seq (.seq br2 I) X)) .ln)
    (s : WordSemStateFiniteExact 64 C F) (g : gcFunConstOk s.gcFun)
    (ok : (evaluate (.seq (.seq (.ite cmp lhs rhs br1 br2) I) X) s).1 ≠ some .error) :
    wordExecutionCost (bP c bg) (constFp (.ite cmp lhs rhs (.seq (.seq br1 I) X) (.seq (.seq br2 I) X))) s ≤
      wordExecutionCost (cfPrice c bg h) (.seq (.seq (.ite cmp lhs rhs br1 br2) I) X) s := by
  have okH : (evaluate (.ite cmp lhs rhs (.seq (.seq br1 I) X) (.seq (.seq br2 I) X)) s).1 ≠ some .error := by
    rw [evaluate_hoist_ite]; exact ok
  have k1 := (constFp_run_cost c hbg h _ hok s g okH).2
  have spQ : ShapePrice (cfPrice (C := C) (F := F) c bg h) := shapePrice_bP c (surShape_add hbg hh)
  have k2 := hoist_ite_cost spQ cmp lhs rhs br1 br2 I X s
  exact le_trans k1 k2

theorem tryIfHoist2_cost (c : Compiler.Encoders.Asm.AsmConfigExact 64) {bg h : WordLangProgHOL (BitVec 64) → Nat}
    (hbg : SurShape bg) (hh : SurShape h) :
    ∀ (N : Nat) (p1 interm dummy p2 p3 : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F),
      tryIfHoist2 N p1 interm dummy p2 = some p3 → HoistOk2 c h N p1 interm dummy p2 →
      gcFunConstOk s.gcFun → (evaluate (.seq (.seq p1 interm) p2) s).1 ≠ some .error →
      wordExecutionCost (bP c bg) p3 s ≤ wordExecutionCost (cfPrice c bg h) (.seq (.seq p1 interm) p2) s := by
  have spQ : ShapePrice (cfPrice (C := C) (F := F) c bg h) := shapePrice_bP c (surShape_add hbg hh)
  have spT := shapePrice_bP (C := C) (F := F) c hbg
  intro N
  induction N with
  | zero => intro p1 interm dummy p2 p3 s hsome; simp [tryIfHoist2] at hsome
  | succ n ih =>
    intro p1 interm dummy p2 p3 s hsome hok g ok
    simp only [tryIfHoist2] at hsome
    cases p1 with
    | ite cmp lhs rhs br1 br2 =>
      simp only [HoistOk2] at hok
      simp only at hsome
      split at hsome
      · cases hsome
      split at hsome
      · cases hsome
      simp only [Option.some.injEq] at hsome
      subst hsome
      exact hoisted_cost c hbg hh cmp lhs rhs br1 br2 interm p2 hok s g ok
    | seq f q =>
      simp only [HoistOk2] at hok
      simp only at hsome
      split at hsome
      · rename_i cmp lhs rhs br1 br2 hd
        have hq : q = .ite cmp lhs rhs br1 br2 := (dest_If_thm q cmp lhs rhs br1 br2).mp hd
        subst hq
        rw [hd] at hok
        dsimp only at hok
        split at hsome
        · cases hsome
        split at hsome
        · cases hsome
        simp only [Option.some.injEq] at hsome
        subst hsome
        -- source: f ; ((ite ; interm) ; p2), by reassociation
        have a1 := (simpLe_seq spQ (simpLe_seq_assoc spQ f (.ite cmp lhs rhs br1 br2) interm) (simpLe_refl p2))
        have a2 := simpLe_seq_assoc spQ f (.seq (.ite cmp lhs rhs br1 br2) interm) p2
        have okA : (evaluate (.seq f (.seq (.seq (.ite cmp lhs rhs br1 br2) interm) p2)) s).1 ≠ some .error := by
          rw [a2.1 s g, a1.1 s g]; exact ok
        have cA := a2.2 s g (by rw [a1.1 s g]; exact ok)
        have cB := a1.2 s g ok
        refine le_trans ?_ (le_trans cA cB)
        rw [wordExecutionCost_seq, wordExecutionCost_seq, spT.seq0, spQ.seq0]
        have mf := wordExecutionCost_mono (bP c bg) (cfPrice c bg h) (preIsel_le_cf c bg h) f s
        rcases hf : evaluate f s with ⟨_ | r, s1⟩
        · dsimp only
          have g1 : gcFunConstOk s1.gcFun := evaluate_gc_fun_const_ok f s none s1 ⟨hf, g⟩
          have ok1 := seq_ok_right okA hf
          have := hoisted_cost c hbg hh cmp lhs rhs br1 br2 interm p2 hok s1 g1 ok1
          omega
        · dsimp only; omega
      · split at hsome
        · rename_i hnone hsimple
          rw [hnone] at hok
          dsimp only at hok
          -- `f ; (q ; interm)` reassociates to `(f ; q) ; interm`
          have a1 := simpLe_seq spQ (simpLe_seq_assoc spQ f q interm) (simpLe_refl p2)
          have okA : (evaluate (.seq (.seq f (.seq q interm)) p2) s).1 ≠ some .error := by
            rw [a1.1 s g]; exact ok
          exact le_trans (ih f (.seq q interm) dummy p2 p3 s hsome hok g okA) (a1.2 s g ok)
        · cases hsome
    | _ => simp at hsome

def HoistOk1 (c : Compiler.Encoders.Asm.AsmConfigExact 64) (h : WordLangProgHOL (BitVec 64) → Nat)
    (p1 p2 : WordLangProgHOL (BitVec 64)) : Prop :=
  match destIf p2 with
  | none => True
  | some (cmp, lhs, rhs, _, _) => HoistOk2 c h rewriteDuplicateIfMaxReassoc p1 .skip (.ite cmp lhs rhs (.raise 1) (.raise 2)) p2

theorem simpLe_seq_skip' {P : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat}
    (sp : ShapePrice P) (a : WordLangProgHOL (BitVec 64)) : SimpLe P a (.seq a .skip) := by
  refine ⟨fun s _ => evaluate_Seq_Skip a s, fun s g ok => ?_⟩
  rw [wordExecutionCost_seq, sp.seq0]
  rcases h : evaluate a s with ⟨_ | r, s1⟩ <;> dsimp only <;> simp [skip_cost sp]

theorem tryIfHoist1_cost (c : Compiler.Encoders.Asm.AsmConfigExact 64) {bg h : WordLangProgHOL (BitVec 64) → Nat}
    (hbg : SurShape bg) (hh : SurShape h) (p1 p2 p3 : WordLangProgHOL (BitVec 64))
    (hsome : tryIfHoist1 p1 p2 = some p3) (hok : HoistOk1 c h p1 p2) (s : WordSemStateFiniteExact 64 C F)
    (g : gcFunConstOk s.gcFun) (ok : (evaluate (.seq p1 p2) s).1 ≠ some .error) :
    wordExecutionCost (bP c bg) p3 s ≤ wordExecutionCost (cfPrice c bg h) (.seq p1 p2) s := by
  have spQ : ShapePrice (cfPrice (C := C) (F := F) c bg h) := shapePrice_bP c (surShape_add hbg hh)
  simp only [tryIfHoist1] at hsome
  simp only [HoistOk1] at hok
  split at hsome
  · cases hsome
  rename_i cmp lhs rhs x y hd
  rw [hd] at hok
  have a1 := simpLe_seq spQ (simpLe_seq_skip' spQ p1) (simpLe_refl p2)
  have okA : (evaluate (.seq (.seq p1 .skip) p2) s).1 ≠ some .error := by rw [a1.1 s g]; exact ok
  exact le_trans (tryIfHoist2_cost c hbg hh _ p1 .skip _ p2 p3 s hsome hok g okA) (a1.2 s g ok)

/-- What `simpDuplicateIf` needs, with total node surcharge budget `sur`: at
every successful hoist the re-applied constant folding is paid by a hoist
surcharge `h`, and the hoists nested inside by the rest `r`, `h + r ≤ sur`. -/
def SdiOk (c : Compiler.Encoders.Asm.AsmConfigExact 64) :
    (WordLangProgHOL (BitVec 64) → Nat) → WordLangProgHOL (BitVec 64) → Prop
  | sur, .mustTerminate q => SdiOk c sur q
  | _, .call none _ _ none => True
  | sur, .call none _ _ (some (_, q2, _, _)) => SdiOk c sur q2
  | sur, .call (some (_, _, q1, _, _)) _ _ none => SdiOk c sur q1
  | sur, .call (some (_, _, q1, _, _)) _ _ (some (_, q2, _, _)) => SdiOk c sur q1 ∧ SdiOk c sur q2
  | sur, .ite _ _ _ a b => SdiOk c sur a ∧ SdiOk c sur b
  | sur, .loop _ b _ => SdiOk c sur b
  | sur, .seq p1 p2 =>
      match tryIfHoist1 (simpDuplicateIf p1) (simpDuplicateIf p2) with
      | none => SdiOk c sur p1 ∧ SdiOk c sur p2
      | some _ => ∃ h r, SurShape h ∧ SurShape r ∧ (∀ q, h q + r q ≤ sur q) ∧
          HoistOk1 c h (simpDuplicateIf p1) (simpDuplicateIf p2) ∧ SdiOk c r p1 ∧ SdiOk c r p2
  | _, _ => True

theorem bP_le_cf (c : Compiler.Encoders.Asm.AsmConfigExact 64) (bg sur : WordLangProgHOL (BitVec 64) → Nat) :
    ∀ (p : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F), bP c bg p s ≤ cfPrice c bg sur p s :=
  preIsel_le_cf c bg sur

/-- `simpDuplicateIf`'s cost transfer: same runs, and its output at the
background price `bP c bg` costs at most the input with the surcharge budget. -/
theorem sdi_cost (c : Compiler.Encoders.Asm.AsmConfigExact 64) :
    ∀ (p : WordLangProgHOL (BitVec 64)) (bg sur : WordLangProgHOL (BitVec 64) → Nat),
      SurShape bg → SurShape sur → SdiOk c sur p →
      Le2 (bP (C := C) (F := F) c bg) (cfPrice c bg sur) p (simpDuplicateIf p)
  | .mustTerminate q, bg, sur, hbg, hs, hok => by
      simp only [SdiOk] at hok
      simp only [simpDuplicateIf]
      refine le2_mustTerminate _ _ (fun s => ?_) (sdi_cost c q bg sur hbg hs hok)
      rw [(shapePrice_bP c hbg).mustTerminate q _ s]; exact bP_le_cf c bg sur _ s
  | .ite cmp lhs rhs a b, bg, sur, hbg, hs, hok => by
      simp only [SdiOk] at hok
      simp only [simpDuplicateIf]
      refine le2_ite _ _ cmp lhs rhs (fun s => ?_) (sdi_cost c a bg sur hbg hs hok.1) (sdi_cost c b bg sur hbg hs hok.2)
      rw [(shapePrice_bP c hbg).ite cmp lhs rhs a b _ _ s]; exact bP_le_cf c bg sur _ s
  | .loop names body exits, bg, sur, hbg, hs, hok => by
      simp only [SdiOk] at hok
      simp only [simpDuplicateIf]
      have ih := sdi_cost c body bg sur hbg hs hok
      refine ⟨fun s g => evaluate_simp_duplicate_if (.loop names body exits) s g, fun s g ok => ?_⟩
      exact loop_cost2 (bP c bg) (cfPrice c bg sur) names exits body _
        (fun s => by rw [(shapePrice_bP c hbg).loop names body _ exits s]; exact bP_le_cf c bg sur _ s)
        ih.1 ih.2 s.clock s rfl g ok
  | .call none dest args none, bg, sur, hbg, hs, hok => by
      simp only [simpDuplicateIf]
      exact ⟨fun _ _ => rfl, fun s _ _ => wordExecutionCost_mono _ _ (bP_le_cf c bg sur) _ s⟩
  | .call none dest args (some (y1, q2, y2, y3)), bg, sur, hbg, hs, hok => by
      simp only [SdiOk] at hok
      simp only [simpDuplicateIf]
      exact le2_callNoneHandler _ _ dest args y1 y2 y3
        (fun s => by rw [(shapePrice_bP c hbg).callHandler none dest args y1 q2 _ y2 y3 s]; exact bP_le_cf c bg sur _ s)
        (fun s g => evaluate_simp_duplicate_if q2 s g)
  | .call (some (x1, x2, q1, x3, x4)) dest args none, bg, sur, hbg, hs, hok => by
      simp only [SdiOk] at hok
      simp only [simpDuplicateIf]
      exact le2_callSome _ _ (bP_le_cf c bg sur) x1 x2 x3 x4 dest args
        (fun s => by rw [(shapePrice_bP c hbg).callRet x1 x2 q1 _ x3 x4 dest args none s]; exact bP_le_cf c bg sur _ s)
        (sdi_cost c q1 bg sur hbg hs hok) (Or.inl ⟨rfl, rfl⟩)
  | .call (some (x1, x2, q1, x3, x4)) dest args (some (y1, q2, y2, y3)), bg, sur, hbg, hs, hok => by
      simp only [SdiOk] at hok
      simp only [simpDuplicateIf]
      exact le2_callSome _ _ (bP_le_cf c bg sur) x1 x2 x3 x4 dest args
        (fun s => by
          rw [(shapePrice_bP c hbg).callRet x1 x2 q1 _ x3 x4 dest args _ s,
            (shapePrice_bP c hbg).callHandler _ dest args y1 q2 _ y2 y3 s]
          exact bP_le_cf c bg sur _ s)
        (sdi_cost c q1 bg sur hbg hs hok.1) (Or.inr ⟨y1, q2, _, y2, y3, rfl, rfl, sdi_cost c q2 bg sur hbg hs hok.2⟩)
  | .seq p1 p2, bg, sur, hbg, hs, hok => by
      have spT := shapePrice_bP (C := C) (F := F) c hbg
      simp only [SdiOk] at hok
      refine ⟨fun s g => evaluate_simp_duplicate_if (.seq p1 p2) s g, fun s g ok => ?_⟩
      simp only [simpDuplicateIf]
      split at hok
      · rename_i hnone
        rw [hnone]
        exact (le2_seq _ _ spT (sdi_cost c p1 bg sur hbg hs hok.1) (sdi_cost c p2 bg sur hbg hs hok.2)).2 s g ok
      · rename_i p3 hsome
        rw [hsome]
        change wordExecutionCost (bP c bg) (WordSimp.seqAssoc .skip p3) s ≤ _
        obtain ⟨h, r, hh, hr, hle, hho, ok1, ok2⟩ := hok
        have hbh := surShape_add hbg hh
        -- inner simplification at background bg + h with budget r
        have i1 := sdi_cost c p1 (fun q => bg q + h q) r hbh hr ok1
        have i2 := sdi_cost c p2 (fun q => bg q + h q) r hbh hr ok2
        have spH := shapePrice_bP (C := C) (F := F) c hbh
        have inner := (le2_seq _ _ spH i1 i2)
        have okx : (evaluate (.seq (simpDuplicateIf p1) (simpDuplicateIf p2)) s).1 ≠ some .error := by
          rw [inner.1 s g]; exact ok
        have k3 : wordExecutionCost (bP c bg) p3 s ≤
            wordExecutionCost (cfPrice c bg h) (.seq (simpDuplicateIf p1) (simpDuplicateIf p2)) s :=
          tryIfHoist1_cost c hbg hh _ _ p3 hsome hho s g okx
        have k4 : wordExecutionCost (bP c (fun q => bg q + h q)) (.seq (simpDuplicateIf p1) (simpDuplicateIf p2)) s ≤
            wordExecutionCost (cfPrice c (fun q => bg q + h q) r) (.seq p1 p2) s := inner.2 s g ok
        have k5 := wordExecutionCost_mono (cfPrice (C := C) (F := F) c (fun q => bg q + h q) r) (cfPrice c bg sur)
          (fun q t => by simp only [cfPrice, bP]; have := hle q; omega) (.seq p1 p2) s
        have e3 : evaluate p3 s = evaluate (.seq p1 p2) s := by
          rw [evaluate_try_if_hoist1 _ _ p3 s hsome g]; exact inner.1 s g
        have k1 := (simpLe_seqAssoc spT p3 .skip).2 s g (by rw [evaluate_Skip_Seq, e3]; exact ok)
        have k2 := (simpLe_skip_seq' spT p3).2 s g (by rw [e3]; exact ok)
        have : wordExecutionCost (cfPrice c bg h) (.seq (simpDuplicateIf p1) (simpDuplicateIf p2)) s =
            wordExecutionCost (bP c (fun q => bg q + h q)) (.seq (simpDuplicateIf p1) (simpDuplicateIf p2)) s := rfl
        omega
  | .skip, bg, sur, _, _, _ | .move _ _, bg, sur, _, _, _ | .inst _, bg, sur, _, _, _ | .assign _ _, bg, sur, _, _, _
  | .get _ _, bg, sur, _, _, _ | .set _ _, bg, sur, _, _, _ | .store _ _, bg, sur, _, _, _ | .alloc _ _, bg, sur, _, _, _
  | .storeConsts _ _ _ _ _, bg, sur, _, _, _ | .raise _, bg, sur, _, _, _ | .return _ _, bg, sur, _, _, _
  | .break _, bg, sur, _, _, _ | .continue _, bg, sur, _, _, _ | .tick, bg, sur, _, _, _
  | .opCurrHeap _ _ _, bg, sur, _, _, _ | .locValue _ _, bg, sur, _, _, _ | .install _ _ _ _ _, bg, sur, _, _, _
  | .codeBufferWrite _ _, bg, sur, _, _, _ | .dataBufferWrite _ _, bg, sur, _, _, _ | .ffi _ _ _ _ _ _, bg, sur, _, _, _
  | .shareInst _ _ _, bg, sur, _, _, _ => by
      simp only [simpDuplicateIf]
      exact ⟨fun _ _ => rfl, fun s _ _ => wordExecutionCost_mono _ _ (bP_le_cf c bg sur) _ s⟩

/-- WordSimp's `compileExp` endpoint: the same run as the source from every
gc-safe state, and its work at the exact selector price is at most the
source's at that price plus 24 per budgeted constant re-assignment (`sur1` for
the first constant folding, `r` for the folding re-applied by
`simpDuplicateIf`). -/
theorem compileExp_run_cost (c : Compiler.Encoders.Asm.AsmConfigExact 64)
    {sur1 r : WordLangProgHOL (BitVec 64) → Nat} (h1 : SurShape sur1) (hr : SurShape r)
    (p : WordLangProgHOL (BitVec 64)) (hcf : CfOk c sur1 (WordSimp.seqAssoc .skip p) .ln)
    (hsdi : SdiOk c r (constFp (WordSimp.seqAssoc .skip p)))
    (s : WordSemStateFiniteExact 64 C F) (g : gcFunConstOk s.gcFun) (ok : (evaluate p s).1 ≠ some .error) :
    evaluate (WordSimp.compileExp p) s = evaluate p s ∧
      wordExecutionCost (preIselPrice c) (WordSimp.compileExp p) s ≤
        wordExecutionCost (bP c (fun q => r q + sur1 q)) p s := by
  have e0 : evaluate (WordSimp.seqAssoc .skip p) s = evaluate p s := evaluate_Seq_assoc p s
  have e1 : evaluate (constFp (WordSimp.seqAssoc .skip p)) s = evaluate p s := by
    rw [evaluate_const_fp _ _ g, e0]
  have e2 : evaluate (simpDuplicateIf (constFp (WordSimp.seqAssoc .skip p))) s = evaluate p s := by
    rw [evaluate_simp_duplicate_if _ _ g, e1]
  refine ⟨by simp only [WordSimp.compileExp]; rw [evaluate_simp_push_out_if, e2], ?_⟩
  simp only [WordSimp.compileExp]
  have spPre := shapePrice_preIsel (C := C) (F := F) c
  -- pushOutIf
  have k3 := (simpLe_pushOutIf spPre (simpDuplicateIf (constFp (WordSimp.seqAssoc .skip p)))).2 s g
    (by rw [e2]; exact ok)
  -- simpDuplicateIf, background 0, budget r
  have k2 := (sdi_cost c (constFp (WordSimp.seqAssoc .skip p)) (fun _ => 0) r surShape_zero_fn hr hsdi).2 s g
    (by rw [e1]; exact ok)
  have k2' : wordExecutionCost (preIselPrice c) (simpDuplicateIf (constFp (WordSimp.seqAssoc .skip p))) s ≤
      wordExecutionCost (bP (C := C) (F := F) c (fun _ => 0)) (simpDuplicateIf (constFp (WordSimp.seqAssoc .skip p))) s :=
    wordExecutionCost_mono _ _ (fun q t => by simp [bP]) _ s
  -- constFp, background r, surcharge sur1
  have hr' : SurShape (fun q => 0 + r q) := surShape_add surShape_zero_fn hr
  have k1 := cf_cost c hr' sur1 (WordSimp.seqAssoc .skip p) .ln s g (csOk_ln s) hcf (by rw [e0]; exact ok)
  have k1' : wordExecutionCost (cfPrice (C := C) (F := F) c (fun _ => 0) r) (constFp (WordSimp.seqAssoc .skip p)) s ≤
      wordExecutionCost (bP c (fun q => 0 + r q)) (constFp (WordSimp.seqAssoc .skip p)) s :=
    wordExecutionCost_mono _ _ (fun q t => by simp [cfPrice, bP]) _ s
  -- seqAssoc at the combined price
  have hall : SurShape (fun q => r q + sur1 q) := surShape_add hr h1
  have spAll := shapePrice_bP (C := C) (F := F) c hall
  have k0 := (simpLe_seqAssoc spAll p .skip).2 s g (by rw [evaluate_Skip_Seq]; exact ok)
  have k0' := (simpLe_skip_seq' spAll p).2 s g ok
  have k1'' : wordExecutionCost (cfPrice (C := C) (F := F) c (fun q => 0 + r q) sur1) (WordSimp.seqAssoc .skip p) s ≤
      wordExecutionCost (bP c (fun q => r q + sur1 q)) (WordSimp.seqAssoc .skip p) s :=
    wordExecutionCost_mono _ _ (fun q t => by simp [cfPrice, bP]) _ s
  simp only [constFp] at k1' k2 k2' k3 ⊢
  omega

#print axioms compileExp_run_cost
#print axioms sdi_cost
#print axioms tryIfHoist1_cost
#print axioms tryIfHoist2_cost
#print axioms hoisted_cost
#print axioms hoist_ite_cost
end InitECandidate.Runtime.FineCost
