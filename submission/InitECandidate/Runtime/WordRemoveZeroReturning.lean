import InitECandidate.Runtime.WordRemoveZeroCalls
namespace InitECandidate.Runtime.WordRemove
open Flapjack Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend.WordRemove

@[simp] theorem zeroState_locals {width : Nat} [NeZero width] {C F : Type}
    (c : WordCompileFn width C) (s : WordSemStateFiniteExact width C F) :
    (compileState 0 c s).locals = s.locals := rfl

/-- Both normal return and installed exception handlers inherit the smaller
clock left by the callee, without adding any destination fuel. -/
theorem zeroRemove_return {width : Nat} [NeZero width] {C F : Type}
    (c : WordCompileFn width C) (n : List Nat) (names : WordLangCutsetsHOL)
    (retHandler : WordLangProgHOL (BitVec width)) (l1 l2 : Nat)
    (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F)
    (next : ∀ child (next : WordSemStateFiniteExact width C F), next.clock < s.clock → ZeroRemoveProp c child next) :
    ZeroRemoveProp c (.call (some (n,names,retHandler,l1,l2)) dest args handler) s := by
  intro r s' h hne hc hd
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [ht] at h
  have hrm : removeMustTerminate
      (WordLangProgHOL.call (some (n, names, retHandler, l1, l2)) dest args handler) =
      .call (some (n, names, removeMustTerminate retHandler, l1, l2)) dest args
        (handler.map (fun hv => (hv.1, removeMustTerminate hv.2.1, hv.2.2.1, hv.2.2.2))) := by
    cases handler with
    | none => rfl
    | some hv => obtain ⟨_, _, _, _⟩ := hv; rfl
  rw [hrm]
  rcases hg : WordSemStateFiniteExact.getVars args s with _ | xs
  · simp only [hg, Prod.mk.injEq] at h
    exact absurd h.1.symm hne
  simp only [hg] at h
  by_cases hbad : wordSemBadDestArgs dest args = true
  · simp only [hbad, if_true, Prod.mk.injEq] at h
    exact absurd h.1.symm hne
  simp only [hbad, Bool.false_eq_true, if_false] at h
  rcases hf : wordSemFindCode dest (wordSemAddRetLoc (some (n, names, retHandler, l1, l2)) xs)
      s.code s.stackSize with _ | ⟨args1, prog, ss⟩
  · simp only [hf, Prod.mk.injEq] at h
    exact absurd h.1.symm hne
  simp only [hf] at h
  simp only [wordSemAddRetLoc] at hf
  by_cases hdc : sptDomainEmpty names.fst ∨ ¬ n.Nodup
  · simp only [hdc, if_true, Prod.mk.injEq] at h
    exact absurd h.1.symm hne
  simp only [hdc, if_false] at h
  rcases hce : wordSemCutEnvs names s.locals with _ | envs
  · simp only [hce, Prod.mk.injEq] at h
    exact absurd h.1.symm hne
  simp only [hce] at h
  have hpm : ∀ (t : WordSemStateFiniteExact width C F),
      pushEnv envs (handler.map (fun hv => (hv.1, removeMustTerminate hv.2.1, hv.2.2.1, hv.2.2.2))) t =
        pushEnv envs handler t := by
    intro t
    cases handler with
    | none => rfl
    | some hv => obtain ⟨_, _, _, _⟩ := hv; rfl
  by_cases hz : s.clock = 0
  · simp only [hz, if_true, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h

    rw [ht, getVars_compileState, hg]
    simp only [hbad, Bool.false_eq_true, if_false, zeroState_code, zeroState_stackSize, findCode_map_I,
      wordSemAddRetLoc, hf, Option.map_some, hdc, zeroState_locals, hce]
    rw [if_pos (by simp [compileState, hz]), hpm, pushEnv_compileState, callEnv_compileState]
    simp only [compileState, flushState, hz]
  simp only [hz, if_false] at h
  rcases hcv : evaluate prog
      (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))) with
    ⟨rc, s2⟩
  rw [hcv] at h
  let callSource := (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s)))
  have hc1 := evaluate_clock prog _ rc s2 hcv
  have entryClock : callSource.clock = s.clock - 1 := by simp only [callSource, WordSemStateFiniteExact.callEnv, pushEnv_clock, decClock]
  have entryDepth : callSource.termdep = s.termdep := by simp only [callSource, WordSemStateFiniteExact.callEnv, pushEnv_termdep, decClock]
  change s2.clock ≤ callSource.clock ∧ s2.termdep = callSource.termdep at hc1
  have hTc : (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))).compile =
      removeCompileRel c := by
    rcases handler with _ | ⟨_, _, _, _⟩ <;> exact hc
  have hcomp := (evaluate_consts prog _ rc s2 hcv).2.2.2.2.1
  have htgt : ∀ k, WordSemStateFiniteExact.callEnv args1 ss
      (pushEnv envs (handler.map (fun hv => (hv.1, removeMustTerminate hv.2.1, hv.2.2.1, hv.2.2.2)))
        (decClock (compileState k c s))) =
      compileState k c
        (WordSemStateFiniteExact.callEnv args1 ss (pushEnv envs handler (decClock s))) := by
    intro k
    rw [← compileState_decClock k c s hz, hpm, pushEnv_compileState, callEnv_compileState]
  rcases rc with _ | ⟨x, ys⟩ | ⟨x, y⟩ | k | k | _ | _ | _ | _
  rotate_left
  · by_cases hx : x ≠ WordLocW.loc l1 l2 ∨ ys.length ≠ n.length
    · simp only [hx, if_true, Prod.mk.injEq] at h
      exact absurd h.1.symm hne
    simp only [hx, if_false] at h
    rcases hp : popEnv s2 with _ | s1
    · simp only [hp, Prod.mk.injEq] at h
      exact absurd h.1.symm hne
    simp only [hp] at h
    have hc2 : s1.clock = s2.clock ∧ s1.termdep = s2.termdep :=
      ⟨popEnv_clock _ _ hp, popEnv_termdep _ _ hp⟩
    have hs1c : s1.compile = s2.compile := by
      unfold popEnv at hp
      split at hp <;> cases hp <;> rfl
    by_cases hdom : sptDomainEqUnion s1.locals envs.fst envs.snd
    · simp only [hdom, if_true] at h
      have hk1 := next prog callSource (by rw [entryClock]; omega) _ _ hcv (by simp) hTc (by rw [entryDepth]; exact hd)
      have hk2 := next retHandler (setVars n ys s1) (by simp only [setVars]; omega) r s' h hne
        (by show s1.compile = _; rw [hs1c, ← hcomp]; exact hTc) (by simp only [setVars]; omega)

      rw [ht, getVars_compileState, hg]
      simp only [hbad, Bool.false_eq_true, if_false, zeroState_code, zeroState_stackSize, findCode_map_I,
        wordSemAddRetLoc, hf, Option.map_some, hdc, zeroState_locals, hce]
      rw [if_neg (by simp only [compileState]; omega), htgt,
        hk1]
      simp only [hx, if_false, popEnv_compileState, hp, Option.map_some, zeroState_locals, hdom,
        if_true, setVars_compileState]
      exact hk2
    · simp only [hdom, if_false, Prod.mk.injEq] at h
      exact absurd h.1.symm hne
  · cases handler with
    | none =>
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hk1 := next prog callSource (by rw [entryClock]; omega) _ _ hcv hne hTc (by rw [entryDepth]; exact hd)

      rw [ht, getVars_compileState, hg]
      simp only [hbad, Bool.false_eq_true, if_false, zeroState_code, zeroState_stackSize, findCode_map_I,
        wordSemAddRetLoc, hf, Option.map_some, hdc, zeroState_locals, hce]
      rw [if_neg (by simp only [compileState]; omega), htgt, hk1]
      rfl
    | some hv =>
      obtain ⟨n', hprog, l1', l2'⟩ := hv
      simp only at h
      by_cases hx : x ≠ WordLocW.loc l1' l2'
      · rw [if_pos hx] at h
        simp only [Prod.mk.injEq] at h
        exact absurd h.1.symm hne
      rw [if_neg hx] at h
      by_cases hdom : sptDomainEqUnion s2.locals envs.fst envs.snd
      · simp only [hdom, if_true] at h
        have hk1 := next prog callSource (by rw [entryClock]; omega) _ _ hcv (by simp) hTc (by rw [entryDepth]; exact hd)
        have hk2 := next hprog (setVar n' y s2) (by simp only [setVar]; omega) r s' h hne
          (by show s2.compile = _; rw [← hcomp]; exact hTc) (by simp only [setVar]; omega)

        have htgt' := htgt 0
        simp only [Option.map_some] at htgt'
        rw [ht, getVars_compileState, hg]
        simp only [hbad, Bool.false_eq_true, if_false, zeroState_code, zeroState_stackSize, findCode_map_I,
          wordSemAddRetLoc, hf, Option.map_some, hdc, zeroState_locals, hce]
        rw [if_neg (by simp only [compileState]; omega), htgt',
          hk1]
        dsimp only
        rw [if_neg hx]
        simp only [zeroState_locals, hdom, if_true, setVar_compileState]
        exact hk2
      · simp only [hdom, if_false, Prod.mk.injEq] at h
        exact absurd h.1.symm hne
  all_goals
    simp only [Prod.mk.injEq] at h
    first
      | exact absurd h.1.symm hne
      | (obtain ⟨rfl, rfl⟩ := h
         have hk1 := next prog callSource (by rw [entryClock]; omega) _ _ hcv hne hTc (by rw [entryDepth]; exact hd)

         rw [ht, getVars_compileState, hg]
         simp only [hbad, Bool.false_eq_true, if_false, zeroState_code, zeroState_stackSize, findCode_map_I,
           wordSemAddRetLoc, hf, Option.map_some, hdc, zeroState_locals, hce]
         rw [if_neg (by simp only [compileState]; omega), htgt, hk1])

#print axioms zeroRemove_return
end InitECandidate.Runtime.WordRemove
