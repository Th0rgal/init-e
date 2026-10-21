import InitECandidate.Runtime.WordIselCall
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact

/-! Returning calls in the instruction-selection transfer. The callee runs as its
selected body from a strictly lower state (callee hypothesis); a matching
result returns through `popEnv` to identical frames and the selected return
continuation; a matching exception enters the selected handler from equal
locals; other outcomes pass through. Cost by `ret_call_cost` on both sides. -/

/-- Selection of a handler option. -/
def selHandler (c : Compiler.Encoders.Asm.AsmConfigExact 64) (temp : Nat) :
    Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat) → Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat)
  | none => none
  | some (a, h, b, d) => some (a, WordInst.instSelectExecutable c temp h, b, d)

theorem isel_retcall_sel (c : Compiler.Encoders.Asm.AsmConfigExact 64) (temp : Nat) (n : List Nat)
    (names : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat) (dest : Option Nat)
    (args : List Nat) (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat)) :
    WordInst.instSelectExecutable c temp (.call (some (n, names, retCode, l1, l2)) dest args handler) =
      .call (some (n, names, WordInst.instSelectExecutable c temp retCode, l1, l2)) dest args
        (selHandler c temp handler) := by
  rcases handler with _ | ⟨a, h, b, d⟩ <;> simp [WordInst.instSelectExecutable, selHandler]

theorem pushEnv_selHandler {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) (temp : Nat)
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64)) (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) : pushEnv envs (selHandler c temp handler) s = pushEnv envs handler s := by
  rcases handler with _ | ⟨a, h, b, d⟩ <;> rfl

theorem popEnv_code {C F : Type} {s p : WordSemStateFiniteExact 64 C F} (h : popEnv s = some p) : p.code = s.code := by
  unfold popEnv at h
  split at h
  · cases h; rfl
  · cases h; rfl
  · cases h

theorem isel_retcall {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) (td ck temp : Nat)
    (n : List Nat) (names : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat) (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (hret : IselGoal (C := C) (F := F) c td ck temp retCode)
    (hhd : ∀ nn hp h1 h2, handler = some (nn, hp, h1, h2) → IselGoal (C := C) (F := F) c td ck temp hp) :
    IselGoal (C := C) (F := F) c td ck temp (.call (some (n, names, retCode, l1, l2)) dest args handler) := by
  intro ih s t res rst le vars rel run ok
  have ht := (evaluate_def_rebound (width := 64) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hargs : ∀ x ∈ args, x < temp := by
    rcases handler with _ | ⟨a, b, c', d⟩ <;>
      simp only [everyVarHOL, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at vars <;> exact vars.1
  have hnm : everyNameHOL (fun x => decide (x < temp)) names = true := by
    rcases handler with _ | ⟨a, b, c', d⟩ <;>
      simp only [everyVarHOL, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at vars <;> exact vars.2.1.1.2
  have hrv : everyVarHOL (fun x => decide (x < temp)) retCode = true := by
    rcases handler with _ | ⟨a, b, c', d⟩ <;>
      simp only [everyVarHOL, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at vars <;> exact vars.2.1.2
  rw [isel_retcall_sel]
  obtain ⟨hl, hcode, hfields⟩ := rel
  have up : UpToLC s t := hfields
  have gv := getVars_rel ⟨hl, hcode, hfields⟩ args hargs
  have ssEq : t.stackSize = s.stackSize := by rw [hfields]
  have ckEq : t.clock = s.clock := by rw [hfields]
  rw [ht] at run
  rcases hg : WordSemStateFiniteExact.getVars args s with _ | xs
  · simp only [hg, Prod.mk.injEq] at run; exact absurd run.1.symm ok
  simp only [hg] at run
  by_cases hbad : wordSemBadDestArgs dest args = true
  · simp only [hbad, if_true, Prod.mk.injEq] at run; exact absurd run.1.symm ok
  have hbad' : wordSemBadDestArgs dest args = false := by simpa using hbad
  simp only [hbad', Bool.false_eq_true, if_false, wordSemAddRetLoc] at run
  rcases hf : wordSemFindCode dest (.loc l1 l2 :: xs) s.code s.stackSize with _ | ⟨args1, prog, ss⟩
  · simp only [hf, Prod.mk.injEq] at run; exact absurd run.1.symm ok
  simp only [hf] at run
  obtain ⟨label, arity, tempF, hlab, hvars, hlabT, hfT⟩ := findCode_rel hcode hf
  by_cases hdc : sptDomainEmpty names.1 ∨ ¬ n.Nodup
  · simp only [hdc, if_true, Prod.mk.injEq] at run; exact absurd run.1.symm ok
  simp only [hdc, if_false] at run
  rcases hce : wordSemCutEnvs names s.locals with _ | envs
  · simp only [hce, Prod.mk.injEq] at run; exact absurd run.1.symm ok
  have hceT := locals_rel_cut_envs temp s.locals t.locals names envs ⟨hl, hnm, hce⟩
  simp only [hce] at run
  have hfT' : wordSemFindCode dest (.loc l1 l2 :: xs) t.code t.stackSize =
      some (args1, WordInst.instSelectExecutable c tempF prog, ss) := by rw [ssEq]; exact hfT
  have tgtRun := ht t (some (n, names, WordInst.instSelectExecutable c temp retCode, l1, l2))
    (selHandler c temp handler) dest args
  rw [gv, hg] at tgtRun
  simp only [hbad', Bool.false_eq_true, if_false, wordSemAddRetLoc, hfT', hdc, hceT, ckEq,
    pushEnv_selHandler] at tgtRun
  have stackMaxEq : (callEnv args1 ss (pushEnv envs handler t)).stackMax =
      (callEnv args1 ss (pushEnv envs handler s)).stackMax := by
    have h := (upToLC_callEnv (upToLC_pushEnv up envs handler) args1 ss).1
    unfold UpToLC at h; rw [h]
  have prices : wordOptimizerLocalPrice (.call (some (n, names, WordInst.instSelectExecutable c temp retCode, l1, l2))
      dest args (selHandler c temp handler)) t ≤ preIselPrice (.call (some (n, names, retCode, l1, l2)) dest args handler) s := by
    rcases handler with _ | ⟨a, b, c', d⟩ <;>
      simp [selHandler, wordOptimizerLocalPrice, preIselPrice, WordToStack.refinedWordLocalPrice,
        WordToStack.refinedWordStackLeafBudget]
  by_cases hz : s.clock = 0
  · simp only [hz, if_true, Prod.mk.injEq] at run tgtRun
    obtain ⟨rfl, rfl⟩ := run
    rw [stackMaxEq] at tgtRun
    refine ⟨_, tgtRun, ⟨?_, ?_, ?_⟩, ?_⟩
    · show WordSemStateFiniteExact.LrPost temp (some .timeOut) _ _
      simp [WordSemStateFiniteExact.LrPost, flushState]
    · simpa [flushState] using hcode
    · simp only [flushState]
      conv_lhs => rw [up]
    · rw [wordExecutionCost, wordExecutionCost]
      simp only [hg, gv, hbad', Bool.false_eq_true, if_false, wordSemAddRetLoc, hf, hfT', hdc, hce, hceT, ckEq, hz,
        dite_true]
      exact prices
  simp only [hz, if_false] at run
  rcases hcv : evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s))) with ⟨rc, s2⟩
  rw [hcv] at run
  -- callee
  obtain ⟨upC, locC⟩ := upToLC_callEnv (upToLC_pushEnv (upToLC_decClock up) envs handler) args1 ss
  have codeC : (callEnv args1 ss (pushEnv envs handler (decClock s))).code = s.code := by
    rcases handler with _ | ⟨a, b, c', d⟩ <;> rfl
  have codeCT : (callEnv args1 ss (pushEnv envs handler (decClock t))).code = t.code := by
    rcases handler with _ | ⟨a, b, c', d⟩ <;> rfl
  have relC : IselRel c tempF (callEnv args1 ss (pushEnv envs handler (decClock s)))
      (callEnv args1 ss (pushEnv envs handler (decClock t))) :=
    ⟨by rw [locC]; exact fun _ _ => rfl, by rw [codeC, codeCT]; exact hcode, upC⟩
  have lex : Prod.Lex (· < ·) (· < ·) ((callEnv args1 ss (pushEnv envs handler (decClock s))).termdep,
      (callEnv args1 ss (pushEnv envs handler (decClock s))).clock) (td, ck) := by
    rcases handler with _ | ⟨a, b, c', d⟩ <;>
      simp only [WordSemStateFiniteExact.callEnv, pushEnv, decClock] <;>
      rcases le with lt | ⟨eq, cle⟩
    all_goals first | exact Prod.Lex.left _ _ lt | (rw [eq]; exact Prod.Lex.right _ (by omega))
  have rcErr : rc ≠ some .error := by
    rintro rfl; simp at run; exact ok run.1.symm
  obtain ⟨s2T, hrunT, postC, costC⟩ := ih label arity tempF prog
    (callEnv args1 ss (pushEnv envs handler (decClock s))) (callEnv args1 ss (pushEnv envs handler (decClock t)))
    rc s2 (by rw [codeC]; exact hlab) hvars (by rw [codeCT]; exact hlabT) lex relC hcv rcErr
  simp only [hz, if_false] at tgtRun
  rw [hrunT] at tgtRun
  have costS := ret_call_cost preIselPrice n names retCode l1 l2 dest args handler s xs hg hbad' args1 prog ss hf hdc
    envs hce hz rc s2 hcv
  have costT := ret_call_cost wordOptimizerLocalPrice n names (WordInst.instSelectExecutable c temp retCode) l1 l2 dest
    args (selHandler c temp handler) t xs (gv.trans hg) hbad' args1 (WordInst.instSelectExecutable c tempF prog) ss hfT'
    hdc envs hceT (by rw [ckEq]; exact hz) rc s2T (by rw [pushEnv_selHandler]; exact hrunT)
  rw [costS, costT, pushEnv_selHandler]
  have up2 : UpToLC s2 s2T := postC.2.2
  have clk2 := evaluate_clock prog _ rc s2 hcv
  have le2 : LexLe s2.termdep s2.clock td ck := by
    have : s2.termdep = s.termdep := by
      rw [clk2.2]; rcases handler with _ | ⟨a, b, c', d⟩ <;> rfl
    have hc2 : s2.clock ≤ s.clock := by
      have := clk2.1; rcases handler with _ | ⟨a, b, c', d⟩ <;>
        simp only [WordSemStateFiniteExact.callEnv, pushEnv, decClock] at this <;> omega
    rcases le with lt | ⟨eq, cle⟩
    · exact Or.inl (this ▸ lt)
    · exact Or.inr ⟨this.trans eq, Nat.le_trans hc2 cle⟩
  rcases rc with _ | (⟨x, ys⟩ | ⟨x, y⟩ | k | k | _ | _ | _ | _)
  · simp at run; exact absurd run.1.symm ok
  · -- result
    simp only at run tgtRun
    by_cases hx : x ≠ WordLocW.loc l1 l2 ∨ ys.length ≠ n.length
    · simp only [hx, if_true, Prod.mk.injEq] at run; exact absurd run.1.symm ok
    simp only [hx, if_false] at run tgtRun
    rcases hp : popEnv s2 with _ | s1
    · simp only [hp, Prod.mk.injEq] at run; exact absurd run.1.symm ok
    obtain ⟨hpT, up1⟩ := upToLC_popEnv up2 hp
    simp only [hp] at run
    rw [hpT] at tgtRun
    simp only at tgtRun
    by_cases hdom : sptDomainEqUnion s1.locals envs.1 envs.2
    · simp only [hdom, if_true] at run tgtRun
      obtain ⟨upV, locV⟩ := upToLC_setVars up1 rfl n ys
      have relV : IselRel c temp (setVars n ys s1) (setVars n ys { s1 with code := s2T.code }) :=
        ⟨by rw [locV]; exact fun _ _ => rfl, by
          show IselCode c s1.code s2T.code
          rw [popEnv_code hp]; exact postC.2.1, upV⟩
      have leV : LexLe (setVars n ys s1).termdep (setVars n ys s1).clock td ck := by
        have e1 : (setVars n ys s1).termdep = s2.termdep := by
          rw [show (setVars n ys s1).termdep = s1.termdep from rfl]
          unfold popEnv at hp; split at hp <;> (try cases hp) <;> rfl
        have e2 : (setVars n ys s1).clock = s2.clock := by
          rw [show (setVars n ys s1).clock = s1.clock from rfl]
          unfold popEnv at hp; split at hp <;> (try cases hp) <;> rfl
        rw [e1, e2]; exact le2
      obtain ⟨rT, hrT, postR, costR⟩ := hret ih _ _ res rst leV hrv relV run ok
      refine ⟨rT, tgtRun.trans hrT, postR, ?_⟩
      simp only [retCont, hx, if_false, hp, hpT, hdom, if_true]
      omega
    · simp only [hdom, if_false, Prod.mk.injEq] at run; exact absurd run.1.symm ok
  · -- exception
    have locEq : s2T.locals = s2.locals := by
      have := postC.1; simp only [WordSemStateFiniteExact.LrPost] at this; exact this.symm
    rcases handler with _ | ⟨nn, hp, h1, h2⟩
    · simp only [selHandler, Prod.mk.injEq] at run tgtRun
      obtain ⟨rfl, rfl⟩ := run
      refine ⟨s2T, by simpa [selHandler] using tgtRun,
        ⟨by simp [WordSemStateFiniteExact.LrPost, locEq], postC.2.1, postC.2.2⟩, ?_⟩
      simp only [retCont, selHandler] at prices ⊢
      omega
    · simp only [selHandler] at tgtRun
      simp only at run tgtRun
      by_cases hx : x ≠ WordLocW.loc h1 h2
      · rw [if_pos hx, Prod.mk.injEq] at run; exact absurd run.1.symm ok
      rw [if_neg hx] at run tgtRun
      by_cases hdom : sptDomainEqUnion s2.locals envs.1 envs.2
      · simp only [hdom, if_true] at run
        rw [locEq] at tgtRun
        simp only [hdom, if_true] at tgtRun
        obtain ⟨upV, locV⟩ := upToLC_setVar up2 locEq nn y
        have relV : IselRel c temp (setVar nn y s2) (setVar nn y s2T) :=
          ⟨by rw [locV]; exact fun _ _ => rfl, postC.2.1, upV⟩
        have leV : LexLe (setVar nn y s2).termdep (setVar nn y s2).clock td ck := le2
        have hpv : everyVarHOL (fun x => decide (x < temp)) hp = true := by
          simp only [everyVarHOL, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at vars
          exact vars.2.2.2
        obtain ⟨rT, hrT, postR, costR⟩ := hhd nn hp h1 h2 rfl ih _ _ res rst leV hpv relV run ok
        refine ⟨rT, tgtRun.trans hrT, postR, ?_⟩
        simp only [retCont, selHandler, hx, if_false, hdom, if_true, locEq] at prices ⊢
        omega
      · simp only [hdom, if_false, Prod.mk.injEq] at run; exact absurd run.1.symm ok
  all_goals
    simp only [Prod.mk.injEq] at run tgtRun
    first
      | exact absurd run.1.symm ok
      | (obtain ⟨rfl, rfl⟩ := run
         refine ⟨s2T, by rw [tgtRun], ⟨lrPost_good (by rfl) postC.1, postC.2.1, postC.2.2⟩, ?_⟩
         simp only [retCont]
         omega)

#print axioms isel_retcall
end InitECandidate.Runtime.FineCost
