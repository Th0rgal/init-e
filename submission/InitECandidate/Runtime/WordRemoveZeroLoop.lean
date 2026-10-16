import InitECandidate.Runtime.WordRemoveZero
namespace InitECandidate.Runtime.WordRemove
open Flapjack Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend.WordRemove

theorem cutState_compiler {width : Nat} [NeZero width] {C F : Type}
    (names : WordLangCutsetsHOL) (s next : WordSemStateFiniteExact width C F)
    (cut : cutState names s = some next) : next.compile = s.compile := by
  unfold cutState at cut
  split at cut
  · cases cut
  · cases cut
    rfl

/-- Actual loop composition at zero term depth needs no added compiler fuel. -/
theorem zeroRemove_loop {width : Nat} [NeZero width] {C F : Type}
    (c : WordCompileFn width C) (names exitNames : WordLangNumSetHOL)
    (body : WordLangProgHOL (BitVec width)) (s : WordSemStateFiniteExact width C F)
    (first : ∀ x, cutState (names,.ln) s = some x → ZeroRemoveProp c body x)
    (next : ∀ x, cutState (names,.ln) s = some x →
      ∀ r1 middle, evaluate body x = (r1,middle) → wordSemContLoop r1 = true →
      middle.clock ≠ 0 → ZeroRemoveProp c (.loop names body exitNames) (decClock middle)) :
    ZeroRemoveProp c (.loop names body exitNames) s := by
  intro r s' h hne hc hd
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [ht] at h
  rw [show removeMustTerminate (WordLangProgHOL.loop names body exitNames) =
    .loop names (removeMustTerminate body) exitNames from rfl]
  rcases hcs : cutState (names, .ln) s with _ | x
  · simp only [hcs, Prod.mk.injEq] at h
    exact absurd h.1.symm hne
  simp only [hcs] at h
  have hcx := cutState_clock_termdep _ _ _ hcs
  have hxc : x.compile = removeCompileRel c := by
    rw [cutState_compiler _ _ _ hcs]; exact hc
  rcases hb : evaluate body x with ⟨r1, s1⟩
  rw [hb] at h
  have hc1 := evaluate_clock body x r1 s1 hb
  have hcomp := (evaluate_consts body x r1 s1 hb).2.2.2.2.1
  by_cases hcont : wordSemContLoop r1 = true
  · simp only [hcont, if_true] at h
    have hr1 : r1 ≠ some .error ∧ r1 ≠ some .timeOut := by
      constructor <;> rintro rfl <;> simp [wordSemContLoop] at hcont
    have hk1 := first x hcs r1 s1 hb hr1.1 hxc (by omega)
    by_cases hz : s1.clock = 0
    · simp only [hz, if_true, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [ht, cutState_compileState, hcs]
      simp only [Option.map_some]
      rw [hk1]
      simp only [hcont, if_true]
      rw [if_pos (by simp [compileState, hz]), flushState_compileState]
    · simp only [hz, if_false] at h
      have hk2 := next x hcs r1 s1 hb hcont hz r s' h hne
        (by show s1.compile = _; rw [← hcomp]; exact hxc) (by simp only [decClock]; omega)
      rw [ht, cutState_compileState, hcs]
      simp only [Option.map_some]
      rw [hk1]
      simp only [hcont, if_true]
      rw [if_neg (by simp only [compileState]; omega), ← compileState_decClock 0 c s1 hz]
      exact hk2
  · simp only [hcont, Bool.false_eq_true, if_false] at h
    have hr1 : r1 ≠ some .error := by
      rintro rfl
      simp only [wordSemExitLoop, Prod.mk.injEq] at h
      exact hne h.1.symm
    have hk1 := first x hcs r1 s1 hb hr1 hxc (by omega)
    rw [ht, cutState_compileState, hcs]
    simp only [Option.map_some]
    rw [hk1]
    simp only [hcont, Bool.false_eq_true, if_false]
    rcases r1 with _ | ⟨_, _⟩ | ⟨_, _⟩ | (_ | k) | k | _ | _ | _ | _ <;>
      simp only [Prod.mk.injEq] at h <;>
      first
        | (obtain ⟨rfl, rfl⟩ := h; rfl)
        | skip
    rw [cutState_compileState]
    rcases hce : cutState (exitNames, .ln) s1 with _ | s2 <;>
      simp only [hce, Option.map_none, Option.map_some, Prod.mk.injEq] at h ⊢
    · obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩
    · obtain ⟨rfl, rfl⟩ := h; exact ⟨rfl, rfl⟩

#print axioms zeroRemove_loop
end InitECandidate.Runtime.WordRemove
