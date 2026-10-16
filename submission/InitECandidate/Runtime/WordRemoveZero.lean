import Flapjack.Compiler.Backend.WordRemove.Proofs.Correct
namespace InitECandidate.Runtime.WordRemove
open Flapjack Flapjack.WordSemStateFiniteExact
open Flapjack.Compiler.Backend.WordRemove

/-- Removal simulation with exactly zero extra fuel at zero term depth. -/
def ZeroRemoveProp {width : Nat} [NeZero width] {C F : Type}
    (compiler : WordCompileFn width C) (p : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) : Prop :=
  ∀ result post, evaluate p s = (result,post) → result ≠ some .error →
    s.compile = removeCompileRel compiler → s.termdep = 0 →
    evaluate (removeMustTerminate p) (compileState 0 compiler s) =
      (result,compileState 0 compiler post)

/-- Clock-constant leaves retain their exact execution and full state image. -/
theorem zeroRemove_leaf {width : Nat} [NeZero width] {C F : Type}
    (compiler : WordCompileFn width C) (p : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) (clockConst : wordProgClockConst p = true)
    (notInstall : ∀ a b d e f, p ≠ .install a b d e f)
    (same : removeMustTerminate p = p) : ZeroRemoveProp compiler p s := by
  intro result post run _ _ _
  rw [same, evaluate_compileState_frame 0 compiler s p clockConst notInstall, run]

/-- At zero term depth, entering MustTerminate is an error, so it cannot be
part of a source execution covered by the compiler's nonerror guarantee. -/
theorem zeroRemove_mustTerminate {width : Nat} [NeZero width] {C F : Type}
    (compiler : WordCompileFn width C) (body : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F) : ZeroRemoveProp compiler (.mustTerminate body) s := by
  intro result post run notError _ zero
  have clause := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.1
  rw [clause] at run
  simp only [zero, if_true, Prod.mk.injEq] at run
  exact (notError run.1.symm).elim

/-- Sequence composition charges no added fuel and uses the real normal-return
state for its second recursive premise. -/
theorem zeroRemove_seq {width : Nat} [NeZero width] {C F : Type}
    (compiler : WordCompileFn width C) (a b : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F)
    (first : ZeroRemoveProp compiler a s)
    (second : ∀ middle, evaluate a s = (none,middle) → ZeroRemoveProp compiler b middle) :
    ZeroRemoveProp compiler (.seq a b) s := by
  intro result post run notError compiled zero
  have clause := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [clause] at run
  rcases actual : evaluate a s with ⟨outcome,middle⟩
  rw [actual] at run
  rw [show removeMustTerminate (.seq a b : WordLangProgHOL (BitVec width)) =
    .seq (removeMustTerminate a) (removeMustTerminate b) from rfl]
  cases outcome with
  | none =>
    dsimp only at run
    have lowered := first none middle actual (by simp) compiled zero
    have middleClock := (evaluate_clock a s none middle actual).2
    have middleCompile := (evaluate_consts a s none middle actual).2.2.2.2.1
    have following := second middle actual result post run notError
      (by rw [← middleCompile]; exact compiled) (by omega)
    rw [clause, lowered]
    exact following
  | some outcome =>
    simp only [Prod.mk.injEq] at run
    obtain ⟨rfl,rfl⟩ := run
    have lowered := first (some outcome) middle actual notError compiled zero
    rw [clause, lowered]

theorem zeroRemove_if {width : Nat} [NeZero width] {C F : Type}
    (compiler : WordCompileFn width C) (cmp : Compiler.Encoders.Asm.HolCmp) (reg : Nat)
    (ri : WordRegImm (BitVec width)) (a b : WordLangProgHOL (BitVec width))
    (s : WordSemStateFiniteExact width C F)
    (yes : ZeroRemoveProp compiler a s) (no : ZeroRemoveProp compiler b s) :
    ZeroRemoveProp compiler (.ite cmp reg ri a b) s := by
  intro result post run notError compiled zero
  have clause := (evaluate_def_rebound (width := width) (C := C) (F := F)).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [clause] at run
  rw [show removeMustTerminate (.ite cmp reg ri a b : WordLangProgHOL (BitVec width)) =
    .ite cmp reg ri (removeMustTerminate a) (removeMustTerminate b) from rfl]
  rcases left : getVar reg s with _ | x
  · simp only [left, Prod.mk.injEq] at run
    exact (notError run.1.symm).elim
  rcases right : getVarImm ri s with _ | y
  · simp only [left, right, Prod.mk.injEq] at run
    exact (notError run.1.symm).elim
  simp only [left, right] at run
  rcases comparison : wordSemWordCmp cmp x y with _ | (_ | _)
  · simp only [comparison, Prod.mk.injEq] at run
    exact (notError run.1.symm).elim
  · simp only [comparison] at run
    rw [clause, getVar_compileState, getVarImm_compileState, left, right]
    simp only [comparison]
    exact no result post run notError compiled zero
  · simp only [comparison] at run
    rw [clause, getVar_compileState, getVarImm_compileState, left, right]
    simp only [comparison]
    exact yes result post run notError compiled zero

#print axioms zeroRemove_if
#print axioms zeroRemove_leaf
#print axioms zeroRemove_mustTerminate
#print axioms zeroRemove_seq
end InitECandidate.Runtime.WordRemove
