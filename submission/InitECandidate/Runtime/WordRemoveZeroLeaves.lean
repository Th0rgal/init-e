import InitECandidate.Runtime.WordRemoveZero
namespace InitECandidate.Runtime.WordRemove
open Flapjack Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend.WordRemove

theorem zeroRemove_tick {width : Nat} [NeZero width] {C F : Type}
    (c : WordCompileFn width C) (s : WordSemStateFiniteExact width C F) :
    ZeroRemoveProp c .tick s := by
  intro r s' h hne hc hd
  have ht := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.1
  rw [ht] at h
  rw [show removeMustTerminate (WordLangProgHOL.tick : WordLangProgHOL (BitVec width)) =
    .tick from rfl, ht]
  by_cases hz : s.clock = 0
  · simp only [hz, if_true, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [if_pos (by simp [compileState, hz]), flushState_compileState]
  · simp only [hz, if_false, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rw [if_neg (by simp [compileState, hz]), compileState_decClock 0 c s hz]

/-- Dynamic installation also commutes with the full zero-clock state image;
the original compiler/oracle relation is retained. -/
theorem zeroRemove_install {width : Nat} [NeZero width] {C F : Type}
    (c : WordCompileFn width C) (s : WordSemStateFiniteExact width C F)
    (ptr len dptr dlen : Nat) (names : WordLangCutsetsHOL) :
    ZeroRemoveProp c (.install ptr len dptr dlen names) s := by
  intro result post run _ compiled _
  rw [show removeMustTerminate (.install ptr len dptr dlen names : WordLangProgHOL (BitVec width)) =
    .install ptr len dptr dlen names from rfl,
    evaluate_install_compileState 0 c s compiled ptr len dptr dlen names, run]

#print axioms zeroRemove_tick
#print axioms zeroRemove_install
end InitECandidate.Runtime.WordRemove
