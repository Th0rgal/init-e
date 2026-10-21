import InitECandidate.Runtime.WordIselCallBase
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Compiler.Backend Flapjack.WordSemStateFiniteExact

/-! Calls in the instruction-selection transfer. A tail call's callee runs over
the target table as its selected body (`findCode_rel`) from a state strictly
below the guard, so the callee hypothesis gives its run and cost; outcomes
other than bad function returns carry equal locals. `ret_call_cost` splits a
returning call's executed cost into node price, callee work and the
continuation (`retCont`). -/

/-- For results other than a bad function return, the post relation on locals
is equality, whatever the temporary. -/
theorem lrPost_good {temp temp' : Nat} {r : Option (WordSemResult 64)} {l l' : Spt (WordLocW 64)}
    (good : wordSemBadFunReturn r = false) (h : WordSemStateFiniteExact.LrPost temp' r l l') :
    WordSemStateFiniteExact.LrPost temp r l l' := by
  rcases r with _ | (_ | _ | _ | _ | _ | _ | _ | _) <;> simp_all [wordSemBadFunReturn, WordSemStateFiniteExact.LrPost]

theorem tail_call_cost {C F : Type} (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (dest : Option Nat) (args : List Nat) (s : WordSemStateFiniteExact 64 C F) (xs : List (WordLocW 64))
    (hg : WordSemStateFiniteExact.getVars args s = some xs) (hbad : wordSemBadDestArgs dest args = false)
    (args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat)
    (hf : wordSemFindCode dest xs s.code s.stackSize = some (args1, prog, ss)) (hz : s.clock ≠ 0) :
    wordExecutionCost price (.call none dest args none) s =
      price (.call none dest args none) s + wordExecutionCost price prog (callEnv args1 ss (decClock s)) := by
  rw [wordExecutionCost]
  simp only [hg, hbad, Bool.false_eq_true, if_false, wordSemAddRetLoc, hf, dif_neg hz]

theorem isel_tailcall {C F : Type} (c : Compiler.Encoders.Asm.AsmConfigExact 64) (td ck temp : Nat)
    (dest : Option Nat) (args : List Nat) : IselGoal (C := C) (F := F) c td ck temp (.call none dest args none) := by
  intro ih s t res rst le vars rel run ok
  have ht := (evaluate_def_rebound (width := 64) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hargs : ∀ x ∈ args, x < temp := by
    simpa [everyVarHOL] using vars
  have sel : WordInst.instSelectExecutable c temp (.call none dest args none) = .call none dest args none := by
    simp [WordInst.instSelectExecutable]
  rw [sel]
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
  simp only [hbad, Bool.false_eq_true, if_false, wordSemAddRetLoc] at run
  rcases hf : wordSemFindCode dest xs s.code s.stackSize with _ | ⟨args1, prog, ss⟩
  · simp only [hf, Prod.mk.injEq] at run; exact absurd run.1.symm ok
  simp only [hf] at run
  obtain ⟨label, arity, tempF, hlab, hvars, hlabT, hfT⟩ := findCode_rel hcode hf
  have hbad' : wordSemBadDestArgs dest args = false := by simpa using hbad
  by_cases hz : s.clock = 0
  · simp only [hz, if_true, Prod.mk.injEq] at run
    obtain ⟨rfl, rfl⟩ := run
    obtain ⟨upF, locF⟩ := upToLC_flush up true
    refine ⟨flushState true t, ?_, ⟨?_, ?_, upF⟩, ?_⟩
    · rw [ht, gv, hg]; simp only [hbad, Bool.false_eq_true, if_false, wordSemAddRetLoc, ssEq, hfT, ckEq, hz, if_true]
    · show WordSemStateFiniteExact.LrPost temp (some .timeOut) _ _
      rw [locF]; exact WordSemStateFiniteExact.lrPost_refl temp _ _
    · simpa [flushState] using hcode
    · rw [wordExecutionCost, wordExecutionCost]
      simp only [hg, gv, hbad, Bool.false_eq_true, if_false, wordSemAddRetLoc, hf, ssEq, hfT, ckEq, hz, dite_true]
      simp [wordOptimizerLocalPrice, preIselPrice, WordToStack.refinedWordLocalPrice,
        WordToStack.refinedWordStackLeafBudget]
  simp only [hz, if_false] at run
  rcases hcv : evaluate prog (callEnv args1 ss (decClock s)) with ⟨rc, s2⟩
  rw [hcv] at run
  simp only at run
  have good : wordSemBadFunReturn rc = false := by
    by_contra hb
    simp only [Bool.not_eq_false] at hb
    simp only [hb, if_true, Prod.mk.injEq] at run; exact ok run.1.symm
  simp only [good, Bool.false_eq_true, if_false, Prod.mk.injEq] at run
  obtain ⟨rfl, rfl⟩ := run
  -- callee states
  obtain ⟨upC, locC⟩ := upToLC_callEnv (upToLC_decClock up) args1 ss
  have codeC : (callEnv args1 ss (decClock s)).code = s.code := rfl
  have codeCT : (callEnv args1 ss (decClock t)).code = t.code := rfl
  have relC : IselRel c tempF (callEnv args1 ss (decClock s)) (callEnv args1 ss (decClock t)) :=
    ⟨by rw [locC]; exact fun _ _ => rfl, by rw [codeC, codeCT]; exact hcode, upC⟩
  have lex : Prod.Lex (· < ·) (· < ·) ((callEnv args1 ss (decClock s)).termdep,
      (callEnv args1 ss (decClock s)).clock) (td, ck) := by
    simp only [WordSemStateFiniteExact.callEnv, decClock]
    rcases le with lt | ⟨eq, cle⟩
    · exact Prod.Lex.left _ _ lt
    · rw [eq]; exact Prod.Lex.right _ (by omega)
  have okC : rc ≠ some .error := by
    intro h; subst h; exact ok rfl
  obtain ⟨s2T, hrunT, postC, costC⟩ := ih label arity tempF prog _ _ rc s2
    (by rw [codeC]; exact hlab) hvars (by rw [codeCT]; exact hlabT) lex relC hcv okC
  refine ⟨s2T, ?_, ⟨lrPost_good good postC.1, postC.2.1, postC.2.2⟩, ?_⟩
  · rw [ht, gv, hg]
    simp only [hbad, Bool.false_eq_true, if_false, wordSemAddRetLoc, ssEq, hfT, ckEq, hz, if_false, hrunT, good]
  · rw [tail_call_cost _ dest args s xs hg hbad' args1 prog ss hf hz,
      tail_call_cost _ dest args t xs (gv.trans hg) hbad' args1 _ ss (by rw [ssEq]; exact hfT) (by rw [ckEq]; exact hz)]
    have pr : wordOptimizerLocalPrice (.call none dest args none) t ≤ preIselPrice (.call none dest args none) s := by
      simp [wordOptimizerLocalPrice, preIselPrice, WordToStack.refinedWordLocalPrice,
        WordToStack.refinedWordStackLeafBudget]
    have decEq : decClock t = { decClock s with locals := t.locals, code := t.code } := by
      have := upToLC_decClock up; exact this
    omega

#print axioms lrPost_good
#print axioms isel_tailcall
/-- Work after a returning call's callee: the return continuation or handler. -/
noncomputable def retCont {C F : Type} (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (n : List Nat) (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (envs : Spt (WordLocW 64) × Spt (WordLocW 64)) :
    Option (WordSemResult 64) → WordSemStateFiniteExact 64 C F → Nat
  | some (.result location returned), middle =>
    if location ≠ .loc l1 l2 ∨ returned.length ≠ n.length then 0 else
      match popEnv middle with
      | none => 0
      | some popped =>
        if sptDomainEqUnion popped.locals envs.1 envs.2 then
          wordExecutionCost price retCode (setVars n returned popped)
        else 0
  | some (.exception location value), middle =>
    match handler with
    | none => 0
    | some (reg, handlerCode, h1, h2) =>
      if location ≠ .loc h1 h2 then 0 else
      if sptDomainEqUnion middle.locals envs.1 envs.2 then
        wordExecutionCost price handlerCode (setVar reg value middle)
      else 0
  | _, _ => 0

theorem ret_call_cost {C F : Type} (price : WordLangProgHOL (BitVec 64) → WordSemStateFiniteExact 64 C F → Nat)
    (n : List Nat) (names : WordLangCutsetsHOL) (retCode : WordLangProgHOL (BitVec 64)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat) (handler : Option (Nat × WordLangProgHOL (BitVec 64) × Nat × Nat))
    (s : WordSemStateFiniteExact 64 C F) (xs : List (WordLocW 64))
    (hg : WordSemStateFiniteExact.getVars args s = some xs) (hbad : wordSemBadDestArgs dest args = false)
    (args1 : List (WordLocW 64)) (prog : WordLangProgHOL (BitVec 64)) (ss : Option Nat)
    (hf : wordSemFindCode dest (.loc l1 l2 :: xs) s.code s.stackSize = some (args1, prog, ss))
    (hdc : ¬ (sptDomainEmpty names.1 ∨ ¬ n.Nodup)) (envs : Spt (WordLocW 64) × Spt (WordLocW 64))
    (hce : wordSemCutEnvs names s.locals = some envs) (hz : s.clock ≠ 0)
    (rc : Option (WordSemResult 64)) (s2 : WordSemStateFiniteExact 64 C F)
    (hcv : evaluate prog (callEnv args1 ss (pushEnv envs handler (decClock s))) = (rc, s2)) :
    wordExecutionCost price (.call (some (n, names, retCode, l1, l2)) dest args handler) s =
      price (.call (some (n, names, retCode, l1, l2)) dest args handler) s +
        wordExecutionCost price prog (callEnv args1 ss (pushEnv envs handler (decClock s))) +
        retCont price n retCode l1 l2 handler envs rc s2 := by
  rw [wordExecutionCost]
  simp only [hg, hbad, Bool.false_eq_true, if_false, wordSemAddRetLoc, hf, hdc, hce, dif_neg hz]
  have hfc : fixClock (callEnv args1 ss (pushEnv envs handler (decClock s))) (rc, s2) = (rc, s2) := by
    rw [← hcv]; exact fix_clock_evaluate _ _
  rw [hcv, hfc]
  rcases rc with _ | (_ | _ | _ | _ | _ | _ | _ | _) <;> simp [retCont]
  split
  · rfl
  · rcases hp : popEnv s2 with _ | p <;> simp
  rcases handler with _ | ⟨reg, hc, h1, h2⟩ <;> simp

#print axioms ret_call_cost
end InitECandidate.Runtime.FineCost
