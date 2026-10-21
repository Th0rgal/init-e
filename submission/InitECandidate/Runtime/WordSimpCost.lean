import InitECandidate.Runtime.WordIselLoop
import InitECandidate.Runtime.WordCallExecutionCost
import InitECandidate.Runtime.WordLineCost
import Flapjack.Compiler.Backend.WordSimp.Proofs.CompileExp
import Flapjack.Compiler.Backend.WordAlloc.Proofs.EvaluateApplyColour.LoopRecursion
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact Flapjack.Compiler.Backend.WordSimp

/-! Same-state cost refinement for the WordSimp passes. Flapjack proves every
WordSimp subpass evaluate-equal from the same state, so a pass is cost-safe when
the rewritten program also does no more work from each state where the original
does not fail. `ShapePrice` collects what the congruences need of a price:
`seq`/`skip` are free and a node's price ignores its sub-programs. -/

variable {C F : Type}

structure ShapePrice (P : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat) : Prop where
  seq0 : ∀ a b s, P (.seq a b) s = 0
  skip0 : ∀ s, P .skip s = 0
  ite : ∀ c r ri a b a' b' s, P (.ite c r ri a' b') s = P (.ite c r ri a b) s
  mustTerminate : ∀ a a' s, P (.mustTerminate a') s = P (.mustTerminate a) s
  loop : ∀ n a a' e s, P (.loop n a' e) s = P (.loop n a e) s
  callRet : ∀ v n a a' l1 l2 d args h s,
    P (.call (some (v, n, a', l1, l2)) d args h) s = P (.call (some (v, n, a, l1, l2)) d args h) s
  callHandler : ∀ r d args x a a' l1 l2 s,
    P (.call r d args (some (x, a', l1, l2))) s = P (.call r d args (some (x, a, l1, l2))) s

/-- `q'` refines `q` at price `P`: from every state with constant-safe GC it
has the same run, and from those where `q` does not fail no more work. -/
def SimpLe (P : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (q q' : WordLangProgHOL (BitVec 64)) : Prop :=
  (∀ s : WordSemStateFiniteExact 64 C F, gcFunConstOk s.gcFun → evaluate q' s = evaluate q s) ∧
  (∀ s : WordSemStateFiniteExact 64 C F, gcFunConstOk s.gcFun → (evaluate q s).1 ≠ some .error →
    wordExecutionCost P q' s ≤ wordExecutionCost P q s)

section
variable {P : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat}

theorem simpLe_refl (q : WordLangProgHOL (BitVec 64)) : SimpLe P q q :=
  ⟨fun _ _ => rfl, fun _ _ _ => Nat.le_refl _⟩

theorem simpLe_trans {q q' q'' : WordLangProgHOL (BitVec 64)} (h1 : SimpLe P q q') (h2 : SimpLe P q' q'') :
    SimpLe P q q'' := by
  refine ⟨fun s g => (h2.1 s g).trans (h1.1 s g), fun s g ok => ?_⟩
  have c1 := h1.2 s g ok
  have c2 := h2.2 s g (by rw [h1.1 s g]; exact ok)
  omega

theorem seq_ok_left {a b : WordLangProgHOL (BitVec 64)} {s : WordSemStateFiniteExact 64 C F}
    (ok : (evaluate (.seq a b) s).1 ≠ some .error) : (evaluate a s).1 ≠ some .error := by
  rw [evaluate_seq_eq] at ok
  rcases h : evaluate a s with ⟨_ | r, s1⟩
  · simp
  · rw [h] at ok; exact ok

theorem seq_ok_right {a b : WordLangProgHOL (BitVec 64)} {s s1 : WordSemStateFiniteExact 64 C F}
    (ok : (evaluate (.seq a b) s).1 ≠ some .error) (h : evaluate a s = (none, s1)) :
    (evaluate b s1).1 ≠ some .error := by
  rw [evaluate_seq_eq, h] at ok; exact ok

theorem simpLe_seq (sp : ShapePrice P) {a a' b b' : WordLangProgHOL (BitVec 64)}
    (ha : SimpLe P a a') (hb : SimpLe P b b') : SimpLe P (.seq a b) (.seq a' b') := by
  refine ⟨fun s g => evaluate_seq_congr_gc s g (ha.1 s g) hb.1, fun s g ok => ?_⟩
  have ca := ha.2 s g (seq_ok_left ok)
  rw [wordExecutionCost_seq, wordExecutionCost_seq, sp.seq0, sp.seq0, ha.1 s g]
  rcases h : evaluate a s with ⟨_ | r, s1⟩
  · have g1 : gcFunConstOk s1.gcFun := evaluate_gc_fun_const_ok a s none s1 ⟨h, g⟩
    have cb := hb.2 s1 g1 (seq_ok_right ok h)
    dsimp only; omega
  · dsimp only; omega

theorem evaluate_ite_congr_gc (cmp : Cmp) (r : Nat) (ri : WordRegImm (BitVec 64))
    {a a' b b' : WordLangProgHOL (BitVec 64)}
    (ha : ∀ s : WordSemStateFiniteExact 64 C F, gcFunConstOk s.gcFun → evaluate a' s = evaluate a s)
    (hb : ∀ s : WordSemStateFiniteExact 64 C F, gcFunConstOk s.gcFun → evaluate b' s = evaluate b s)
    (s : WordSemStateFiniteExact 64 C F) (g : gcFunConstOk s.gcFun) :
    evaluate (.ite cmp r ri a' b') s = evaluate (.ite cmp r ri a b) s := by
  have ht := (evaluate_def_rebound (width := 64) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [ht, ht, ha s g, hb s g]

theorem simpLe_ite (sp : ShapePrice P) (cmp : Cmp) (r : Nat) (ri : WordRegImm (BitVec 64))
    {a a' b b' : WordLangProgHOL (BitVec 64)} (ha : SimpLe P a a') (hb : SimpLe P b b') :
    SimpLe P (.ite cmp r ri a b) (.ite cmp r ri a' b') := by
  have ht := (evaluate_def_rebound (width := 64) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨evaluate_ite_congr_gc cmp r ri ha.1 hb.1, fun s g ok => ?_⟩
  rw [ht] at ok
  rw [wordExecutionCost, wordExecutionCost, sp.ite cmp r ri a b a' b' s]
  rcases hx : getVar r s with _ | x
  · simp
  rcases hy : getVarImm ri s with _ | y
  · simp
  rw [hx, hy] at ok
  dsimp only at ok ⊢
  rcases hc : wordSemWordCmp cmp x y with _ | _ | _
  · simp
  · rw [hc] at ok
    have := hb.2 s g ok
    dsimp only; omega
  · rw [hc] at ok
    have := ha.2 s g ok
    dsimp only; omega

theorem evaluate_mustTerminate_congr_gc {a a' : WordLangProgHOL (BitVec 64)}
    (ha : ∀ s : WordSemStateFiniteExact 64 C F, gcFunConstOk s.gcFun → evaluate a' s = evaluate a s)
    (s : WordSemStateFiniteExact 64 C F) (g : gcFunConstOk s.gcFun) :
    evaluate (.mustTerminate a') s = evaluate (.mustTerminate a) s := by
  have ht := (evaluate_def_rebound (width := 64) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
  rw [ht, ht]
  generalize hL : wordSemMustTerminateLimit 64 = L
  rw [ha { s with clock := L, termdep := s.termdep - 1 } g]

theorem simpLe_mustTerminate (sp : ShapePrice P) {a a' : WordLangProgHOL (BitVec 64)} (ha : SimpLe P a a') :
    SimpLe P (.mustTerminate a) (.mustTerminate a') := by
  have ht := (evaluate_def_rebound (width := 64) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨evaluate_mustTerminate_congr_gc ha.1, fun s g ok => ?_⟩
  rw [ht] at ok
  rw [wordExecutionCost, wordExecutionCost, sp.mustTerminate a a' s]
  by_cases hz : s.termdep = 0
  · simp only [hz, dite_true]; exact Nat.le_refl _
  simp only [hz, if_false, dite_false] at ok ⊢
  generalize hL : wordSemMustTerminateLimit 64 = L at ok ⊢
  have okb : (evaluate a { s with clock := L, termdep := s.termdep - 1 }).1 ≠ some .error := by
    rcases hb : evaluate a { s with clock := L, termdep := s.termdep - 1 } with ⟨r, s1⟩
    rw [hb] at ok
    rintro rfl; simp at ok
  have := ha.2 { s with clock := L, termdep := s.termdep - 1 } g okb
  omega

/-- Right-association of `seq`. -/
theorem simpLe_seq_assoc (sp : ShapePrice P) (a b c : WordLangProgHOL (BitVec 64)) :
    SimpLe P (.seq (.seq a b) c) (.seq a (.seq b c)) := by
  refine ⟨fun s _ => (evalEq_seq_assoc a b c s).symm, fun s g ok => ?_⟩
  rw [wordExecutionCost_seq, wordExecutionCost_seq, wordExecutionCost_seq, sp.seq0, sp.seq0, sp.seq0,
    evaluate_seq_eq]
  rcases h : evaluate a s with ⟨_ | r, s1⟩
  · dsimp only
    rw [wordExecutionCost_seq, sp.seq0]
    rcases h2 : evaluate b s1 with ⟨_ | r2, s2⟩ <;> dsimp only <;> omega
  · dsimp only; omega

/-- Left-association of `seq`. -/
theorem simpLe_seq_assoc' (sp : ShapePrice P) (a b c : WordLangProgHOL (BitVec 64)) :
    SimpLe P (.seq a (.seq b c)) (.seq (.seq a b) c) := by
  refine ⟨fun s _ => evalEq_seq_assoc a b c s, fun s g ok => ?_⟩
  rw [wordExecutionCost_seq, wordExecutionCost_seq, wordExecutionCost_seq, sp.seq0, sp.seq0, sp.seq0,
    evaluate_seq_eq]
  rcases h : evaluate a s with ⟨_ | r, s1⟩
  · dsimp only
    rw [wordExecutionCost_seq, sp.seq0]
    rcases h2 : evaluate b s1 with ⟨_ | r2, s2⟩ <;> dsimp only <;> omega
  · dsimp only; omega

theorem skip_cost (sp : ShapePrice P) (s : WordSemStateFiniteExact 64 C F) :
    wordExecutionCost P .skip s = 0 := by
  rw [wordCost_leaf _ rfl]; exact sp.skip0 s

theorem simpLe_skip_seq (sp : ShapePrice P) (a : WordLangProgHOL (BitVec 64)) :
    SimpLe P (.seq .skip a) a := by
  refine ⟨fun s _ => (evaluate_Skip_Seq a s).symm, fun s g ok => ?_⟩
  rw [wordExecutionCost_seq, sp.seq0, skip_cost sp, evaluate_skip_eq]
  dsimp only; omega

theorem simpLe_skip_seq' (sp : ShapePrice P) (a : WordLangProgHOL (BitVec 64)) :
    SimpLe P a (.seq .skip a) := by
  refine ⟨fun s _ => evaluate_Skip_Seq a s, fun s g ok => ?_⟩
  rw [wordExecutionCost_seq, sp.seq0, skip_cost sp, evaluate_skip_eq]
  dsimp only; omega

theorem simpLe_seq_skip (sp : ShapePrice P) (a : WordLangProgHOL (BitVec 64)) :
    SimpLe P (.seq a .skip) a := by
  refine ⟨fun s _ => (evaluate_Seq_Skip a s).symm, fun s g ok => ?_⟩
  rw [wordExecutionCost_seq, sp.seq0]
  rcases h : evaluate a s with ⟨_ | r, s1⟩ <;> dsimp only <;> omega

theorem simpLe_smartSeq (sp : ShapePrice P) (a b : WordLangProgHOL (BitVec 64)) :
    SimpLe P (.seq a b) (smartSeqHOL a b) := by
  cases a
  case skip => exact simpLe_skip_seq sp b
  all_goals exact simpLe_refl _

theorem simpLe_loop_cost (sp : ShapePrice P) (names exits : WordLangNumSetHOL) {body body' : WordLangProgHOL (BitVec 64)}
    (hb : SimpLe P body body') :
    ∀ (n : Nat) (s : WordSemStateFiniteExact 64 C F), s.clock = n → gcFunConstOk s.gcFun →
      (evaluate (.loop names body exits) s).1 ≠ some .error →
      wordExecutionCost P (.loop names body' exits) s ≤ wordExecutionCost P (.loop names body exits) s := by
  have ht := (evaluate_def_rebound (width := 64) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
  intro s hn g ok
  rcases hcs : cutState (names, .ln) s with _ | cs
  · rw [loop_cost_cut_none P names body' exits s hcs, loop_cost_cut_none P names body exits s hcs,
      sp.loop names body body' exits s]
  have gcs : gcFunConstOk cs.gcFun := by
    obtain ⟨l, rfl⟩ := cutStateConst _ _ _ hcs; exact g
  rcases hbr : evaluate body cs with ⟨r1, s1⟩
  have hbT : evaluate body' cs = (r1, s1) := (hb.1 cs gcs).trans hbr
  rw [ht, hcs] at ok
  dsimp only at ok
  rw [hbr] at ok
  dsimp only at ok
  have okb : (evaluate body cs).1 ≠ some .error := by
    rw [hbr]; rintro rfl
    simp [wordSemContLoop, wordSemExitLoop] at ok
  have kb := hb.2 cs gcs okb
  rw [loop_cost_clause P names body exits s cs hcs r1 s1 hbr, loop_cost_clause P names body' exits s cs hcs r1 s1 hbT,
    sp.loop names body body' exits s]
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

theorem simpLe_loop (sp : ShapePrice P) (names exits : WordLangNumSetHOL) {body body' : WordLangProgHOL (BitVec 64)}
    (hb : SimpLe P body body') : SimpLe P (.loop names body exits) (.loop names body' exits) :=
  ⟨fun s g => evaluate_Loop_body_cong_gc (fun f => gcFunConstOk f) s names body body' exits
      (fun v gv => hb.1 v gv) g,
   fun s g ok => simpLe_loop_cost sp names exits hb s.clock s rfl g ok⟩

/-- Returning calls with their return continuation and handler program
replaced: the callee runs from the identical state (`pushEnv` ignores the
handler program), so only the selected continuation's work differs. -/
theorem simpLe_callSome (sp : ShapePrice P) (v : List Nat) (names : WordLangCutsetsHOL)
    {k k' : WordLangProgHOL (BitVec 64)} (l1 l2 : Nat) (dest : Option Nat) (args : List Nat)
    {h h' : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat)}
    (hk : SimpLe P k k')
    (hh : (h = none ∧ h' = none) ∨ ∃ x hp hp' a b, h = some (x, hp, a, b) ∧ h' = some (x, hp', a, b) ∧
      SimpLe P hp hp') :
    SimpLe P (.call (some (v, names, k, l1, l2)) dest args h) (.call (some (v, names, k', l1, l2)) dest args h') := by
  have ht := (evaluate_def_rebound (width := 64) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hpush : ∀ (envs : Spt (WordLocW 64) × Spt (WordLocW 64)) (x : WordSemStateFiniteExact 64 C F),
      pushEnv envs h' x = pushEnv envs h x := by
    rcases hh with ⟨rfl, rfl⟩ | ⟨x, hp, hp', a, b, rfl, rfl, -⟩ <;> intros <;> rfl
  have hpr : ∀ x : WordSemStateFiniteExact 64 C F,
      P (.call (some (v, names, k', l1, l2)) dest args h') x = P (.call (some (v, names, k, l1, l2)) dest args h) x := by
    intro x
    rw [sp.callRet v names k k' l1 l2 dest args h' x]
    rcases hh with ⟨rfl, rfl⟩ | ⟨y, hp, hp', a, b, rfl, rfl, -⟩
    · rfl
    · exact sp.callHandler _ dest args y hp hp' a b x
  constructor
  · intro s g
    have e1 := evalEq_call_ret_gc (fun w gw => (hk.1 w gw).symm) v names l1 l2 dest args h s g
    rw [e1]
    rcases hh with ⟨rfl, rfl⟩ | ⟨y, hp, hp', a, b, rfl, rfl, hph⟩
    · rfl
    · exact (evalEq_call_handler_gc (fun w gw => (hph.1 w gw).symm) _ dest args y a b s g).symm
  intro s g ok
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
    exact le_of_eq (hpr s)
  simp only [hz, if_false] at ok
  rcases hcv : evaluate prog (callEnv args1 ss (pushEnv envs h (decClock s))) with ⟨rc, s2⟩
  rw [hcv] at ok
  have hcvT : evaluate prog (callEnv args1 ss (pushEnv envs h' (decClock s))) = (rc, s2) := by
    rw [hpush]; exact hcv
  have g2 : gcFunConstOk s2.gcFun := by
    rw [← (evaluate_consts prog _ _ s2 hcv).1, gcFun_callEnv_pushEnv]; exact g
  rw [ret_call_cost P v names k l1 l2 dest args h s xs hg hbad' args1 prog ss hf hdc envs hce hz rc s2 hcv,
    ret_call_cost P v names k' l1 l2 dest args h' s xs hg hbad' args1 prog ss hf hdc envs hce hz rc s2 hcvT,
    hpush, hpr s]
  apply Nat.add_le_add_left
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

/-- A call without return continuation and with a handler program replaced:
the handler is never run (the call fails to set up), so only the price is
charged. -/
theorem simpLe_callNoneHandler (sp : ShapePrice P) (dest : Option Nat) (args : List Nat) (x : Nat)
    {hp hp' : WordLangProgHOL (BitVec 64)} (a b : Nat) (hph : SimpLe P hp hp') :
    SimpLe P (.call none dest args (some (x, hp, a, b))) (.call none dest args (some (x, hp', a, b))) := by
  refine ⟨fun s g => (evalEq_call_handler_gc (fun w gw => (hph.1 w gw).symm) none dest args x a b s g).symm,
    fun s g ok => ?_⟩
  rw [wordExecutionCost, wordExecutionCost]
  have hE := sp.callHandler none dest args x hp hp' a b s
  rcases hg : WordSemStateFiniteExact.getVars args s with _ | xs
  · simp only; exact le_of_eq hE
  simp only
  by_cases hbad : wordSemBadDestArgs dest args = true
  · simp only [hbad, if_true]; exact le_of_eq hE
  simp only [hbad, Bool.false_eq_true, if_false, wordSemAddRetLoc]
  rcases hf : wordSemFindCode dest xs s.code s.stackSize with _ | ⟨args1, prog, ss⟩
  all_goals simp only; exact le_of_eq hE

theorem seqAssoc_leaf (sp : ShapePrice P) (q : WordLangProgHOL (BitVec 64)) (hq : isLeafProg q = true)
    (hs : q ≠ .skip) (p1 : WordLangProgHOL (BitVec 64)) : SimpLe P (.seq p1 q) (WordSimp.seqAssoc p1 q) := by
  have : WordSimp.seqAssoc p1 q = smartSeqHOL p1 q := by
    cases q <;> simp only [isLeafProg, Bool.false_eq_true] at hq
    case skip => exact absurd rfl hs
    all_goals rw [WordSimp.seqAssoc]
    all_goals (intros; simp_all)
  rw [this]; exact simpLe_smartSeq sp p1 q

/-- `WordSimp.seqAssoc p1 q` refines `seq p1 q`. -/
theorem simpLe_seqAssoc (sp : ShapePrice P) :
    ∀ (q p1 : WordLangProgHOL (BitVec 64)), SimpLe P (.seq p1 q) (WordSimp.seqAssoc p1 q)
  | .skip, p1 => by rw [WordSimp.seqAssoc]; exact simpLe_seq_skip sp p1
  | .seq q1 q2, p1 => by
      rw [WordSimp.seqAssoc]
      exact simpLe_trans (simpLe_seq_assoc' sp p1 q1 q2)
        (simpLe_trans (simpLe_seq sp (simpLe_seqAssoc sp q1 p1) (simpLe_refl q2))
          (simpLe_seqAssoc sp q2 (WordSimp.seqAssoc p1 q1)))
  | .ite c r ri q1 q2, p1 => by
      rw [WordSimp.seqAssoc]
      have h1 := simpLe_trans (simpLe_skip_seq' sp q1) (simpLe_seqAssoc sp q1 .skip)
      have h2 := simpLe_trans (simpLe_skip_seq' sp q2) (simpLe_seqAssoc sp q2 .skip)
      exact simpLe_trans (simpLe_seq sp (simpLe_refl p1) (simpLe_ite sp c r ri h1 h2)) (simpLe_smartSeq sp _ _)
  | .mustTerminate q, p1 => by
      rw [WordSimp.seqAssoc]
      have h := simpLe_trans (simpLe_skip_seq' sp q) (simpLe_seqAssoc sp q .skip)
      exact simpLe_trans (simpLe_seq sp (simpLe_refl p1) (simpLe_mustTerminate sp h)) (simpLe_smartSeq sp _ _)
  | .loop names body exits, p1 => by
      rw [WordSimp.seqAssoc]
      have h := simpLe_trans (simpLe_skip_seq' sp body) (simpLe_seqAssoc sp body .skip)
      exact simpLe_trans (simpLe_seq sp (simpLe_refl p1) (simpLe_loop sp names exits h)) (simpLe_smartSeq sp _ _)
  | .call ret dest args handler, p1 => by
      rcases ret with _ | ⟨x1, x2, k, x3, x4⟩ <;> rcases handler with _ | ⟨y1, hq, y2, y3⟩ <;>
        rw [WordSimp.seqAssoc] <;>
        refine simpLe_trans (simpLe_seq sp (simpLe_refl p1) ?_) (simpLe_smartSeq sp _ _)
      · exact simpLe_refl _
      · exact simpLe_callNoneHandler sp dest args y1 y2 y3
          (simpLe_trans (simpLe_skip_seq' sp hq) (simpLe_seqAssoc sp hq .skip))
      · exact simpLe_callSome sp x1 x2 x3 x4 dest args
          (simpLe_trans (simpLe_skip_seq' sp k) (simpLe_seqAssoc sp k .skip)) (Or.inl ⟨rfl, rfl⟩)
      · exact simpLe_callSome sp x1 x2 x3 x4 dest args
          (simpLe_trans (simpLe_skip_seq' sp k) (simpLe_seqAssoc sp k .skip))
          (Or.inr ⟨y1, hq, _, y2, y3, rfl, rfl,
            simpLe_trans (simpLe_skip_seq' sp hq) (simpLe_seqAssoc sp hq .skip)⟩)
  | .move a b, p1 => seqAssoc_leaf sp (.move a b) rfl nofun p1
  | .inst a, p1 => seqAssoc_leaf sp (.inst a) rfl nofun p1
  | .assign a b, p1 => seqAssoc_leaf sp (.assign a b) rfl nofun p1
  | .get a b, p1 => seqAssoc_leaf sp (.get a b) rfl nofun p1
  | .set a b, p1 => seqAssoc_leaf sp (.set a b) rfl nofun p1
  | .store a b, p1 => seqAssoc_leaf sp (.store a b) rfl nofun p1
  | .alloc a b, p1 => seqAssoc_leaf sp (.alloc a b) rfl nofun p1
  | .storeConsts a b c d e, p1 => seqAssoc_leaf sp (.storeConsts a b c d e) rfl nofun p1
  | .raise a, p1 => seqAssoc_leaf sp (.raise a) rfl nofun p1
  | .return a b, p1 => seqAssoc_leaf sp (.return a b) rfl nofun p1
  | .break a, p1 => seqAssoc_leaf sp (.break a) rfl nofun p1
  | .continue a, p1 => seqAssoc_leaf sp (.continue a) rfl nofun p1
  | .tick, p1 => seqAssoc_leaf sp (.tick) rfl nofun p1
  | .opCurrHeap a b c, p1 => seqAssoc_leaf sp (.opCurrHeap a b c) rfl nofun p1
  | .locValue a b, p1 => seqAssoc_leaf sp (.locValue a b) rfl nofun p1
  | .install a b c d e, p1 => seqAssoc_leaf sp (.install a b c d e) rfl nofun p1
  | .codeBufferWrite a b, p1 => seqAssoc_leaf sp (.codeBufferWrite a b) rfl nofun p1
  | .dataBufferWrite a b, p1 => seqAssoc_leaf sp (.dataBufferWrite a b) rfl nofun p1
  | .ffi a b c d e f, p1 => seqAssoc_leaf sp (.ffi a b c d e f) rfl nofun p1
  | .shareInst a b c, p1 => seqAssoc_leaf sp (.shareInst a b c) rfl nofun p1

theorem pushOut_cost (sp : ShapePrice P) :
    ∀ (p : WordLangProgHOL (BitVec 64)) (s : WordSemStateFiniteExact 64 C F), gcFunConstOk s.gcFun →
      (evaluate p s).1 ≠ some .error → wordExecutionCost P (pushOutIfAux p).1 s ≤ wordExecutionCost P p s
  | .mustTerminate q, s, g, ok => by
      have i : SimpLe P q (pushOutIfAux q).1 := ⟨fun v _ => evaluate_push_out_if_aux q v, pushOut_cost sp q⟩
      rcases hq : pushOutIfAux q with ⟨c, bq⟩
      rw [hq] at i
      simp only [pushOutIfAux, hq]
      exact (simpLe_mustTerminate sp i).2 s g ok
  | .seq c1 c2, s, g, ok => by
      have i1 : SimpLe P c1 (pushOutIfAux c1).1 := ⟨fun v _ => evaluate_push_out_if_aux c1 v, pushOut_cost sp c1⟩
      have i2 : SimpLe P c2 (pushOutIfAux c2).1 := ⟨fun v _ => evaluate_push_out_if_aux c2 v, pushOut_cost sp c2⟩
      rcases h1 : pushOutIfAux c1 with ⟨c1', b1⟩
      rcases h2 : pushOutIfAux c2 with ⟨c2', b2⟩
      rw [h1] at i1; rw [h2] at i2
      rcases b1 <;> simp only [pushOutIfAux, h1, h2]
      · exact (simpLe_seq sp i1 i2).2 s g ok
      · exact (simpLe_seq sp i1 (simpLe_refl c2)).2 s g ok
  | .loop names body exits, s, g, ok => by
      have i : SimpLe P body (pushOutIfAux body).1 :=
        ⟨fun v _ => evaluate_push_out_if_aux body v, pushOut_cost sp body⟩
      simp only [pushOutIfAux]
      exact (simpLe_loop sp names exits i).2 s g ok
  | .ite cmp r1 ri c1 c2, s, g, ok => by
      have ht := (evaluate_def_rebound (width := 64) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      have i1 : SimpLe P c1 (pushOutIfAux c1).1 := ⟨fun v _ => evaluate_push_out_if_aux c1 v, pushOut_cost sp c1⟩
      have i2 : SimpLe P c2 (pushOutIfAux c2).1 := ⟨fun v _ => evaluate_push_out_if_aux c2 v, pushOut_cost sp c2⟩
      rcases h1 : pushOutIfAux c1 with ⟨c1', b1⟩
      rcases h2 : pushOutIfAux c2 with ⟨c2', b2⟩
      rw [h1] at i1; rw [h2] at i2
      dsimp only at i1 i2
      rcases b1 <;> rcases b2 <;> simp only [pushOutIfAux, h1, h2]
      · exact (simpLe_ite sp cmp r1 ri i1 i2).2 s g ok
      · -- `c2'` never falls through; `c1'` moves after the `ite`
        rw [ht] at ok
        rw [wordExecutionCost_seq, sp.seq0, wordExecutionCost, wordExecutionCost,
          sp.ite cmp r1 ri c1 c2 .skip c2' s, ht]
        rcases hx : getVar r1 s with _ | x
        · simp
        rcases hy : getVarImm ri s with _ | y
        · simp
        rw [hx, hy] at ok
        dsimp only at ok ⊢
        rcases hc : wordSemWordCmp cmp x y with _ | _ | _
        · simp
        · rw [hc] at ok
          have k2 := i2.2 s g ok
          dsimp only
          rcases hev : evaluate c2' s with ⟨rr, s1⟩
          have hr := push_out_if_aux_T c2 c2' rr s s1 h2 (by rw [← i2.1 s g]; exact hev)
          rcases rr with _ | rr
          · exact absurd rfl hr
          · dsimp only; omega
        · rw [hc] at ok
          have k1 := i1.2 s g ok
          rw [skip_cost sp, evaluate_skip_eq]
          dsimp only; omega
      · -- `c1'` never falls through; `c2'` moves after the `ite`
        rw [ht] at ok
        rw [wordExecutionCost_seq, sp.seq0, wordExecutionCost, wordExecutionCost,
          sp.ite cmp r1 ri c1 c2 c1' .skip s, ht]
        rcases hx : getVar r1 s with _ | x
        · simp
        rcases hy : getVarImm ri s with _ | y
        · simp
        rw [hx, hy] at ok
        dsimp only at ok ⊢
        rcases hc : wordSemWordCmp cmp x y with _ | _ | _
        · simp
        · rw [hc] at ok
          have k2 := i2.2 s g ok
          rw [skip_cost sp, evaluate_skip_eq]
          dsimp only; omega
        · rw [hc] at ok
          have k1 := i1.2 s g ok
          dsimp only
          rcases hev : evaluate c1' s with ⟨rr, s1⟩
          have hr := push_out_if_aux_T c1 c1' rr s s1 h1 (by rw [← i1.1 s g]; exact hev)
          rcases rr with _ | rr
          · exact absurd rfl hr
          · dsimp only; omega
      · exact (simpLe_ite sp cmp r1 ri i1 i2).2 s g ok
  | .call ret dest args handler, s, _, _ => by
      cases ret <;> simp only [pushOutIfAux] <;> exact Nat.le_refl _
  | .skip, _, _, _ | .move _ _, _, _, _ | .inst _, _, _, _ | .assign _ _, _, _, _ | .get _ _, _, _, _
  | .set _ _, _, _, _ | .store _ _, _, _, _ | .alloc _ _, _, _, _ | .storeConsts _ _ _ _ _, _, _, _
  | .raise _, _, _, _ | .return _ _, _, _, _ | .break _, _, _, _ | .continue _, _, _, _ | .tick, _, _, _
  | .opCurrHeap _ _ _, _, _, _ | .locValue _ _, _, _, _ | .install _ _ _ _ _, _, _, _
  | .codeBufferWrite _ _, _, _, _ | .dataBufferWrite _ _, _, _, _ | .ffi _ _ _ _ _ _, _, _, _
  | .shareInst _ _ _, _, _, _ => by simp only [pushOutIfAux]; exact Nat.le_refl _

theorem simpLe_pushOutIf (sp : ShapePrice P) (p : WordLangProgHOL (BitVec 64)) : SimpLe P p (pushOutIf p) :=
  ⟨fun s _ => evaluate_push_out_if_aux p s, pushOut_cost sp p⟩

end

#print axioms simpLe_pushOutIf
#print axioms simpLe_seqAssoc
#print axioms simpLe_loop
#print axioms simpLe_callSome
#print axioms simpLe_callNoneHandler
#print axioms simpLe_seq
#print axioms simpLe_ite
#print axioms simpLe_mustTerminate
#print axioms simpLe_seq_assoc
#print axioms simpLe_smartSeq
end InitECandidate.Runtime.FineCost
