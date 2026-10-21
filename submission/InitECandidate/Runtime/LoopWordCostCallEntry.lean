import InitECandidate.Runtime.LoopWordCostCallBase
import Flapjack.Pancake.LoopToWord.Proofs.CompileCorrect.Call
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact

/-! The Word state at the entry of a compiled returning call, following the
pinned `compile_correct` call cases. -/

/-- Word facts of a returning call whose Loop arguments, callee and entry cut
succeed. -/
theorem ret_call_entry {C F : Type} {s entry : LoopSemStateFiniteExact 64 F} {t : WordSemStateFiniteExact 64 C F}
    {ctxt : Spt Nat} {retv : WordLocW 64} (l : Nat × Nat)
    {names : List Nat} {live : NumSet} {target : Option Nat} {arguments : List Nat}
    {values env prog}
    (rel : loopToWordStateRelHOLExact s t) (locals : LoopToWord.localsRelHOL ctxt s.locals t.locals)
    (ret : sptLookup 0 t.locals = some retv) (namesCtxt : ∀ k, k ∈ names → sptMem k ctxt)
    (args : LoopSemStateFiniteExact.getVars arguments s = some values)
    (find : LoopSemStateFiniteExact.findCode target values s.code = some (env, prog))
    (nodup : names.Nodup) (cut : LoopSemStateFiniteExact.cutRes live (none, s) = (none, entry)) :
    ∃ args1 ss1 ctxt1 l1 result,
      getVars (arguments.map (LoopToWord.findVarHOL ctxt)) t = some values ∧
      wordSemBadDestArgs target (arguments.map (LoopToWord.findVarHOL ctxt)) = false ∧
      (∀ R : WordLangProgHOL (BitVec 64), wordSemFindCode target
        (wordSemAddRetLoc (some (names.map (LoopToWord.findVarHOL ctxt),
          ((LoopToWord.mkNewCutsetHOL ctxt live, .ln) : WordLangCutsetsHOL), R, l.1, l.2)) values)
        t.code t.stackSize = some (args1, (LoopToWord.compHOL ctxt1 prog l1).1, ss1)) ∧
      ¬ sptDomainEmpty (LoopToWord.mkNewCutsetHOL ctxt live) ∧
      (names.map (LoopToWord.findVarHOL ctxt)).Nodup ∧
      wordSemCutEnvs (LoopToWord.mkNewCutsetHOL ctxt live, .ln) t.locals = some (result, .ln) ∧
      t.clock ≠ 0 ∧
      entry = LoopSemStateFiniteExact.decClock { s with locals := sptInter s.locals live } ∧
      LoopToWord.localsRelHOL ctxt (sptInter s.locals live) result ∧ sptLookup 0 result = some retv ∧
      (∀ H, loopToWordStateRelHOLExact { entry with locals := env }
          (callEnv args1 ss1 (pushEnv (result, .ln) H (decClock t))) ∧
        LoopToWord.localsRelHOL ctxt1 env (callEnv args1 ss1 (pushEnv (result, .ln) H (decClock t))).locals ∧
        sptLookup 0 (callEnv args1 ss1 (pushEnv (result, .ln) H (decClock t))).locals =
          some (.loc l.1 l.2)) ∧
      (∀ k, sptMem k (accVarsHOL prog .ln) → sptMem k ctxt1) := by
  have rel' := rel
  obtain ⟨len, hm, hmd, hsmd, hclock, hbe, hffi, hcur, hlen, htop, hglob, hcode⟩ := rel'
  obtain ⟨hwgv, -⟩ := LoopToWord.localsRelHOLGetVars ctxt s t arguments values ⟨locals, args⟩
  obtain ⟨args1, ss1, ctxt1, l1, hwf, h0, hl1, hacc1⟩ :=
    LoopToWord.CompileCorrect.findCode_rel s.code t.code t.stackSize target values env prog
      (.loc l.1 l.2) hcode find
  have hbad : wordSemBadDestArgs target (arguments.map (LoopToWord.findVarHOL ctxt)) = false := by
    cases target with
    | some _ => simp [wordSemBadDestArgs]
    | none =>
      cases arguments with
      | nil =>
        simp [LoopSemStateFiniteExact.getVars] at args
        subst args
        simp [LoopSemStateFiniteExact.findCode] at find
      | cons _ _ => simp [wordSemBadDestArgs]
  have hne : ¬ sptDomainEmpty (LoopToWord.mkNewCutsetHOL ctxt live) := fun h =>
    LoopToWord.domainMkNewCutsetNotEmpty ctxt live
      (funext fun k => propext ⟨fun hk => h k hk, False.elim⟩)
  have hndw : (names.map (LoopToWord.findVarHOL ctxt)).Nodup :=
    LoopToWord.localsRelHOLAllDistinctMap ctxt s.locals t.locals names ⟨locals, namesCtxt, nodup⟩
  unfold LoopSemStateFiniteExact.cutRes at cut
  simp only at cut
  cases hcs : LoopSemStateFiniteExact.cutState live s with
  | none => simp [hcs] at cut
  | some cs =>
    simp only [hcs] at cut
    unfold LoopSemStateFiniteExact.cutState at hcs
    split at hcs
    · rename_i hsub
      cases hcs
      by_cases hz : s.clock = 0
      · simp [hz] at cut
      simp only [hz, if_false, Prod.mk.injEq, true_and] at cut
      subst cut
      obtain ⟨result, hce, hlr⟩ := LoopToWord.wordSemCutEnvMkNewCutsetHOL ctxt live s.locals
        t.locals retv ⟨locals, hsub, ret⟩
      refine ⟨args1, ss1, ctxt1, l1, result, hwgv, hbad, fun R => hwf, hne, hndw,
        LoopToWord.wordSemCutEnvLNIMPHOL _ _ _ hce, by rw [hclock]; exact hz, rfl, hlr,
        (LoopToWord.wordSemCutEnvMkNewCutsetIMPHOL ctxt live t.locals result hce).trans ret,
        fun H => ⟨?_, hl1, h0⟩, hacc1⟩
      rcases H with _ | ⟨a, b, c, d⟩ <;>
        simp only [loopToWordStateRelHOLExact, WordSemStateFiniteExact.callEnv, pushEnv, decClock,
          LoopSemStateFiniteExact.decClock] <;>
        exact ⟨len, hm, hmd, hsmd, by omega, hbe, hffi, hcur, hlen, htop, hglob, hcode⟩
    · cases hcs

#print axioms ret_call_entry
end InitECandidate.Runtime.FineCost
