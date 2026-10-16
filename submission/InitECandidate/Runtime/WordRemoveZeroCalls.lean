import InitECandidate.Runtime.WordRemoveZeroLoop
namespace InitECandidate.Runtime.WordRemove
open Flapjack Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend.WordRemove

@[simp] theorem zeroState_code {width : Nat} [NeZero width] {C F : Type}
    (c : WordCompileFn width C) (s : WordSemStateFiniteExact width C F) :
    (compileState 0 c s).code = sptMap (fun p => (p.1,removeMustTerminate p.2)) s.code := rfl
@[simp] theorem zeroState_stackSize {width : Nat} [NeZero width] {C F : Type}
    (c : WordCompileFn width C) (s : WordSemStateFiniteExact width C F) :
    (compileState 0 c s).stackSize = s.stackSize := rfl

theorem zeroRemove_tail {width : Nat} [NeZero width] {C F : Type}
    (c : WordCompileFn width C) (dest : Option Nat) (args : List Nat)
    (handler : Option (Nat × WordLangProgHOL (BitVec width) × Nat × Nat))
    (s : WordSemStateFiniteExact width C F)
    (next : ∀ actualArgs body ss, s.clock ≠ 0 →
      ZeroRemoveProp c body (WordSemStateFiniteExact.callEnv actualArgs ss (decClock s))) :
    ZeroRemoveProp c (.call none dest args handler) s := by
  intro r s' h hne hc hd
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  rw [ht] at h
  rcases hg : WordSemStateFiniteExact.getVars args s with _ | xs
  · simp only [hg, Prod.mk.injEq] at h
    exact absurd h.1.symm hne
  simp only [hg] at h
  by_cases hbad : wordSemBadDestArgs dest args = true
  · simp only [hbad, if_true, Prod.mk.injEq] at h
    exact absurd h.1.symm hne
  simp only [hbad, Bool.false_eq_true, if_false] at h
  rcases hf : wordSemFindCode dest (wordSemAddRetLoc (none : Option (List Nat × WordLangCutsetsHOL × WordLangProgHOL (BitVec width) × Nat × Nat)) xs) s.code s.stackSize with
    _ | ⟨args1, prog, ss⟩
  · simp only [hf, Prod.mk.injEq] at h
    exact absurd h.1.symm hne
  simp only [hf] at h
  cases handler with
  | some hv =>
    simp only [Prod.mk.injEq] at h
    exact absurd h.1.symm hne
  | none =>
    simp only at h
    rw [show removeMustTerminate (WordLangProgHOL.call none dest args none) =
      (.call none dest args none : WordLangProgHOL (BitVec width)) from rfl]
    by_cases hz : s.clock = 0
    · simp only [hz, if_true, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [ht, getVars_compileState, hg]
      simp only [hbad, Bool.false_eq_true, if_false, zeroState_code, zeroState_stackSize, findCode_map_I, hf,
        Option.map_some]
      rw [if_pos (by simp [compileState, hz]), flushState_compileState]
    · simp only [hz, if_false] at h
      rcases hcv : evaluate prog (WordSemStateFiniteExact.callEnv args1 ss (decClock s)) with
        ⟨rc, sc⟩
      rw [hcv] at h
      have hc1 := evaluate_clock prog _ rc sc hcv
      by_cases hb : wordSemBadFunReturn rc = true
      · simp only [hb, if_true, Prod.mk.injEq] at h
        exact absurd h.1.symm hne
      simp only [hb, Bool.false_eq_true, if_false, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hk := next args1 prog ss hz _ sc hcv hne (by exact hc) (by simpa only [Flapjack.WordSemStateFiniteExact.callEnv, decClock] using hd)
      rw [ht, getVars_compileState, hg]
      simp only [hbad, Bool.false_eq_true, if_false, zeroState_code, zeroState_stackSize, findCode_map_I, hf,
        Option.map_some]
      rw [if_neg (by simp only [compileState]; omega), ← compileState_decClock 0 c s hz,
        callEnv_compileState, hk]
      simp only [hb, Bool.false_eq_true, if_false]

#print axioms zeroRemove_tail
end InitECandidate.Runtime.WordRemove
