import InitECandidate.Runtime.LoopWordP
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.WordSemStateFiniteExact

/-! Label-indexed Loop-to-Word cost transfer: static compiler labels. `compHOL`
threads the return labels `(fn, k)` through the Loop program independently of
the variable context; a function body is compiled at `(name, 2)`, where the
callee `name` is determined by the actual call (its explicit target or the code
location carried by the last argument value). -/

/-- `compHOL`'s label output does not depend on the variable context. -/
theorem compHOL_labels_ctxt (c1 c2 : Spt Nat) :
    ∀ (p : HolLoopProg 64) (l : Nat × Nat), (LoopToWord.compHOL c1 p l).2 = (LoopToWord.compHOL c2 p l).2
  | .seq a b, l => by
      rw [LoopToWord.compHOL.eq_def, LoopToWord.compHOL.eq_def]; dsimp only
      rw [compHOL_labels_ctxt c1 c2 a l]; exact compHOL_labels_ctxt c1 c2 b _
  | .ite _ _ _ a b _, l => by
      rw [LoopToWord.compHOL.eq_def, LoopToWord.compHOL.eq_def]; dsimp only
      rw [compHOL_labels_ctxt c1 c2 a l]; exact compHOL_labels_ctxt c1 c2 b _
  | .loop _ b _, l => by
      rw [LoopToWord.compHOL.eq_def, LoopToWord.compHOL.eq_def]; dsimp only; exact compHOL_labels_ctxt c1 c2 b l
  | .mark b, l => by rw [LoopToWord.compHOL.eq_def, LoopToWord.compHOL.eq_def]; exact compHOL_labels_ctxt c1 c2 b l
  | .call r t a h, l => by
      rw [LoopToWord.compHOL.eq_def, LoopToWord.compHOL.eq_def]
      rcases r with _ | ⟨vs, live⟩
      · rfl
      · rcases h with _ | ⟨n, p1, p2, lo⟩
        · rfl
        · dsimp only
          rw [compHOL_labels_ctxt c1 c2 p1 _, compHOL_labels_ctxt c1 c2 p2 _]
  | .primitive ds op as, l => by
      rw [LoopToWord.compHOL.eq_def, LoopToWord.compHOL.eq_def]; dsimp only; split <;> rfl
  | .arith op, l => by
      rw [LoopToWord.compHOL.eq_def, LoopToWord.compHOL.eq_def]; cases op <;> rfl
  | .skip, _ | .assign _ _, _ | .store _ _, _ | .setGlobal _ _, _ | .load32 _ _, _
  | .loadByte _ _, _ | .store32 _ _, _ | .storeByte _ _, _ | .break _, _ | .continue _, _ | .raise _, _
  | .return _, _ | .shMem _ _ _, _ | .tick, _ | .fail, _ | .locValue _ _, _ | .ffi _ _ _ _ _ _, _ => by
      rw [LoopToWord.compHOL.eq_def, LoopToWord.compHOL.eq_def]

/-- The label after compiling `p` from `l` (context-independent). -/
noncomputable def labAfter (p : HolLoopProg 64) (l : Nat × Nat) : Nat × Nat := (LoopToWord.compHOL (.ln : Spt Nat) p l).2

theorem compHOL_labAfter (ctxt : Spt Nat) (p : HolLoopProg 64) (l : Nat × Nat) :
    (LoopToWord.compHOL ctxt p l).2 = labAfter p l := compHOL_labels_ctxt ctxt .ln p l

/-- The function a call reaches: its explicit target, or the code location in
the last argument value (an indirect call). -/
def calleeName {width : Nat} [NeZero width] : Option Nat → List (WordLocW width) → Nat
  | some p, _ => p
  | none, args => match args.getLast? with
    | some (.loc loc 0) => loc
    | _ => 0

open Flapjack.LoopToWord.CompileCorrect Flapjack.LoopToWord in
theorem findCode_relL {width : Nat} [NeZero width]
    (scode : Spt (List Nat × HolLoopProg width))
    (tcode : Spt (Nat × WordLangProgHOL (BitVec width))) (ssize : Spt Nat)
    (dest : Option Nat) (argvals : List (WordLocW width)) (env : Spt (WordLocW width))
    (prog : HolLoopProg width) (x : WordLocW width)
    (hcode : loopToWordCodeRelHOLExact scode tcode)
    (hf : LoopSemStateFiniteExact.findCode dest argvals scode = some (env, prog)) :
    ∃ args1 ss1 ctxt1,
      wordSemFindCode dest (x :: argvals) tcode ssize =
          some (args1, (LoopToWord.compHOL ctxt1 prog (calleeName dest argvals, 2)).1, ss1) ∧
        sptLookup 0 (sptFromList2 args1) = some x ∧
        LoopToWord.localsRelHOL ctxt1 env (sptFromList2 args1) ∧
        ∀ k, sptMem k (accVarsHOL prog .ln) → sptMem k ctxt1 := by
  cases dest with
  | some p =>
    simp only [LoopSemStateFiniteExact.findCode] at hf
    split at hf
    · cases hf
    · rename_i params body hlk
      split at hf
      · rename_i hlen
        simp only [Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, rfl⟩ := hf
        obtain ⟨htl, hnd⟩ := hcode p params body hlk
        obtain ⟨hl, hacc⟩ := LoopToWord.CompileCorrect.compFunc_ctxt params body argvals x hnd hlen.symm
        refine ⟨x :: argvals, sptLookup p ssize, _, ?_, ?_, hl, hacc⟩
        · simp [wordSemFindCode, htl, hlen, loopToWordCompFuncHOL, calleeName]
        · have h := sptLookup_sptFromList2_get (x :: argvals) 0 (by simp)
          simp only [Nat.mul_zero, List.getElem_cons_zero] at h; exact h
      · cases hf
  | none =>
    cases argvals with
    | nil => simp [LoopSemStateFiniteExact.findCode] at hf
    | cons a rest =>
      simp only [LoopSemStateFiniteExact.findCode] at hf
      split at hf
      · rename_i loc hlast
        split at hf
        · cases hf
        · rename_i params body hlk
          split at hf
          · rename_i hlen
            simp only [Option.some.injEq, Prod.mk.injEq] at hf
            obtain ⟨rfl, rfl⟩ := hf
            obtain ⟨htl, hnd⟩ := hcode loc params body hlk
            have hlen' : params.length = (a :: rest).dropLast.length := by
              simp at hlen ⊢; omega
            obtain ⟨hl, hacc⟩ := LoopToWord.CompileCorrect.compFunc_ctxt params body (a :: rest).dropLast x hnd hlen'
            have hname : calleeName none (a :: rest) = loc := by
              simp only [calleeName, List.getLast?_eq_some_getLast (List.cons_ne_nil a rest), hlast]
            rw [hname]
            refine ⟨x :: (a :: rest).dropLast, sptLookup loc ssize, _, ?_, ?_, hl, hacc⟩
            · have hl2 : (x :: a :: rest).getLast (by simp) = .loc loc 0 := by
                rw [List.getLast_cons (by simp)]; exact hlast
              simp only [wordSemFindCode, List.cons_ne_nil, dite_false, hl2, htl]
              rw [if_pos (by simp at hlen ⊢; omega)]
              simp [loopToWordCompFuncHOL, List.dropLast_cons_of_ne_nil]
            · have h := sptLookup_sptFromList2_get (x :: (a :: rest).dropLast) 0 (by simp)
              simp only [Nat.mul_zero, List.getElem_cons_zero] at h; exact h
          · cases hf
      · cases hf


theorem ret_call_entryL {C F : Type} {s entry : LoopSemStateFiniteExact 64 F} {t : WordSemStateFiniteExact 64 C F}
    {ctxt : Spt Nat} {retv : WordLocW 64} (l : Nat × Nat)
    {names : List Nat} {live : NumSet} {target : Option Nat} {arguments : List Nat}
    {values env prog}
    (rel : loopToWordStateRelHOLExact s t) (locals : LoopToWord.localsRelHOL ctxt s.locals t.locals)
    (ret : sptLookup 0 t.locals = some retv) (namesCtxt : ∀ k, k ∈ names → sptMem k ctxt)
    (args : LoopSemStateFiniteExact.getVars arguments s = some values)
    (find : LoopSemStateFiniteExact.findCode target values s.code = some (env, prog))
    (nodup : names.Nodup) (cut : LoopSemStateFiniteExact.cutRes live (none, s) = (none, entry)) :
    ∃ args1 ss1 ctxt1 result,
      getVars (arguments.map (LoopToWord.findVarHOL ctxt)) t = some values ∧
      wordSemBadDestArgs target (arguments.map (LoopToWord.findVarHOL ctxt)) = false ∧
      (∀ R : WordLangProgHOL (BitVec 64), wordSemFindCode target
        (wordSemAddRetLoc (some (names.map (LoopToWord.findVarHOL ctxt),
          ((LoopToWord.mkNewCutsetHOL ctxt live, .ln) : WordLangCutsetsHOL), R, l.1, l.2)) values)
        t.code t.stackSize = some (args1, (LoopToWord.compHOL ctxt1 prog (calleeName target values, 2)).1, ss1)) ∧
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
  obtain ⟨args1, ss1, ctxt1, hwf, h0, hl1, hacc1⟩ :=
    findCode_relL s.code t.code t.stackSize target values env prog
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
      refine ⟨args1, ss1, ctxt1, result, hwgv, hbad, fun R => hwf, hne, hndw,
        LoopToWord.wordSemCutEnvLNIMPHOL _ _ _ hce, by rw [hclock]; exact hz, rfl, hlr,
        (LoopToWord.wordSemCutEnvMkNewCutsetIMPHOL ctxt live t.locals result hce).trans ret,
        fun H => ⟨?_, hl1, h0⟩, hacc1⟩
      rcases H with _ | ⟨a, b, c, d⟩ <;>
        simp only [loopToWordStateRelHOLExact, WordSemStateFiniteExact.callEnv, pushEnv, decClock,
          LoopSemStateFiniteExact.decClock] <;>
        exact ⟨len, hm, hmd, hsmd, by omega, hbe, hffi, hcur, hlen, htop, hglob, hcode⟩
    · cases hcs


#print axioms findCode_relL
#print axioms ret_call_entryL
#print axioms compHOL_labels_ctxt
end InitECandidate.Runtime.FineCost
