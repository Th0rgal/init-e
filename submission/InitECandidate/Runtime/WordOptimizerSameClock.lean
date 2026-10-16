import InitECandidate.Runtime.WordRemoveZeroCorrect
import Flapjack.Compiler.Backend.WordToWord.Proofs.CompileWordToWord
namespace InitECandidate.Runtime.WordToWord
open Flapjack Flapjack.WordSemStateFiniteExact Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.WordToWord Flapjack.Compiler.Backend.WordRemove

open Classical in
/-- Full Word optimizer transfer at zero term depth preserves the exact initial
fuel. The original code, compiler, oracle, GC, and permutation premises remain. -/
theorem compile_word_to_word_same_clock {width : Nat} [NeZero width] {C F : Type}
    (st : WordSemStateFiniteExact width C F) (l : Spt (Nat × WordLangProgHOL (BitVec width)))
    (cc : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) →
      Option (List (BitVec 8) × List (BitVec width) × C))
    (coracle : Nat → C × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (tt : Bool) (kk aa : Nat) (co : AsmConfigExact width) (start : Nat) (zero : st.termdep = 0) :
    codeRel st.code l ∧ sptDomain st.code = sptDomain l ∧
      st.compile = (fun conf progs => cc conf (progs.map (fun p => fullCompileSingle tt kk aa co (p, none)))) ∧
      coracle = Prod.map id (List.map (fun p => fullCompileSingle tt kk aa co (p, none))) ∘ st.compileOracle ∧
      Compiler.Backend.WordSimp.gcFunConstOk st.gcFun →
    ∃ (perm' : Nat → Nat → Nat),
      let prog : WordLangProgHOL (BitVec width) := .call none (some start) [0] none
      let (res, rst) := evaluate prog { st with permute := perm' }
      if res = some .error then True
      else
        let (res1, rst1) := evaluate prog
          { st with
            code := sptMap (fun p => (p.1, removeMustTerminate p.2)) l
            clock := st.clock
            termdep := 0
            compile := cc
            compileOracle := coracle }
        res1 = res ∧ rst1.clock = rst.clock ∧ rst1.ffi = rst.ffi ∧ rst1.stackMax = rst.stackMax := by
  rintro ⟨hrel, hdom, hcomp, rfl, hgc⟩
  let rmt : Nat × Nat × WordLangProgHOL (BitVec width) → Nat × Nat × WordLangProgHOL (BitVec width) :=
    fun t => (t.1, t.2.1, removeMustTerminate t.2.2)
  let cc' : C → List (Nat × Nat × WordLangProgHOL (BitVec width)) →
      Option (List (BitVec 8) × List (BitVec width) × C) := fun conf => cc conf ∘ List.map rmt
  let O' := Prod.map id (List.map (fun p => compileSingle tt kk aa co (p, none))) ∘ st.compileOracle
  have hcomp' : st.compile =
      (fun conf progs => cc' conf (progs.map (fun p => compileSingle tt kk aa co (p, none)))) := by
    rw [hcomp]
    funext conf progs
    simp only [cc', Function.comp, List.map_map]
    rfl
  let prog : WordLangProgHOL (BitVec width) := .call none (some start) [0] none
  obtain ⟨perm', H⟩ := compile_single_correct tt kk aa co prog st l O' cc' ⟨hrel, hdom, hcomp', rfl, hgc⟩
  refine ⟨perm', ?_⟩
  rcases hA : evaluate prog { st with permute := perm' } with ⟨res, rst⟩
  rw [hA] at H
  dsimp only at H
  by_cases herr : res = some .error
  · show (match evaluate prog { st with permute := perm' } with
      | (res, rst) => if res = some .error then True else _)
    rw [hA]
    simp [herr]
  rw [if_neg herr] at H
  rcases hB : evaluate prog { st with code := l, compileOracle := O', compile := cc' } with ⟨res1, rst1⟩
  rw [hB] at H
  dsimp only at H
  obtain ⟨hres, -, -, hs1⟩ := H
  subst hres
  have hW := WordRemove.zeroRemove_correct cc prog {st with code := l, compileOracle := O', compile := cc'}
    res1 rst1 hB herr rfl zero
  have hst : ({ st with
      code := sptMap (fun p => (p.1, removeMustTerminate p.2)) l
      clock := st.clock
      termdep := 0
      compile := cc
      compileOracle := Prod.map id (List.map (fun p => fullCompileSingle tt kk aa co (p, none))) ∘
        st.compileOracle } : WordSemStateFiniteExact width C F) =
      compileState 0 cc { st with code := l, compileOracle := O', compile := cc' } := by
    simp only [compileState, Nat.add_zero]
    congr 1
    funext k
    simp only [O', Function.comp, Prod.map, List.map_map, id]
    rfl
  show (match evaluate prog { st with permute := perm' } with
    | (res, rst) => if res = some .error then True else _)
  rw [hA]
  dsimp only
  rw [if_neg herr, hst, show (WordLangProgHOL.call none (some start) [0] none : WordLangProgHOL (BitVec width)) =
    removeMustTerminate prog from rfl, hW]
  refine ⟨rfl, ?_, ?_, ?_⟩ <;> rw [hs1] <;> rfl

#print axioms compile_word_to_word_same_clock
end InitECandidate.Runtime.WordToWord
