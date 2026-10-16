import InitECandidate.Runtime.StackEntryBudget
import Flapjack.Compiler.Backend.StackNames.Proofs.MakeInit
import Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

namespace InitECandidate.Runtime.StackNames
open Flapjack Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.StackNames

/-- The actual initialized source state renames back to the supplied target
state, including its clock. No runtime execution is hidden in this equality. -/
theorem rename_makeInit_eq {width : Nat} [NeZero width] {C F : Type}
    (s : StackSemStateFiniteExact width C F) (f : Spt Nat) (code : List (Nat × HolProg width))
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (hf : Function.Bijective (findNameSpt f))
    (hcode : s.code = sptFromAList (compileHOL f code))
    (hor : s.compileOracle = Prod.map id (Prod.map (compileHOL f) id) ∘ oracle) :
    renameState s.compile f (makeInit f (sptFromAList code) oracle s) = s := by
  have hinv : ∀ y, findNameSpt f (holLinv (findNameSpt f) (fun _ => True) y) = y :=
    apply_holLinv_of_surjective hf.2
  have hc : sptFromAList (compileHOL f (sptToAList (sptFromAList code))) = s.code := by
    rw [hcode]
    refine (sptEqThm _ _ ⟨sptWfFromAList _, sptWfFromAList _⟩).mpr fun n => ?_
    rw [sptLookup_sptFromAList, sptAListLookup_compileHOL, ← sptLookup_sptFromAList,
      sptLookup_sptFromAList_sptToAList, sptLookup_sptFromAList, sptLookup_sptFromAList,
      sptAListLookup_compileHOL]
  classical
  have hsave : (fun y => decide (∃ x, decide (∃ z, s.ffiSaveRegs z = true ∧
      x = holLinv (findNameSpt f) (fun _ => True) z) = true ∧ y = findNameSpt f x)) =
      s.ffiSaveRegs := by
    funext y
    by_cases hy : s.ffiSaveRegs y = true
    · rw [hy, decide_eq_true_iff]
      exact ⟨holLinv (findNameSpt f) (fun _ => True) y,
        decide_eq_true_iff.mpr ⟨y, hy, rfl⟩, (hinv y).symm⟩
    · rw [Bool.not_eq_true] at hy
      rw [hy, decide_eq_false_iff_not]
      rintro ⟨x, hx, rfl⟩
      obtain ⟨z, hz, rfl⟩ := decide_eq_true_iff.mp hx
      rw [hinv z, hz] at hy
      exact Bool.noConfusion hy
  simp only [renameState, makeInit, MakeInit.mapKeys_mapKeys_linv hf, hc, ← hor]
  refine Eq.trans ?_ (show { s with ffiSaveRegs := s.ffiSaveRegs } = s from rfl)
  congr 1

/-- Register naming transmits a concrete evaluation at the identical initial
fuel; result, final FFI and remaining clock are preserved exactly. -/
theorem initialized_evaluate_same_clock {width : Nat} [NeZero width] {C F : Type}
    (target : StackSemStateFiniteExact width C F) (names : Spt Nat)
    (code : List (Nat × HolProg width))
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (prog : HolProg width) (fuel : Nat) (result : Option (StackSemResult width))
    (post : StackSemStateFiniteExact width C F)
    (bijective : Function.Bijective (findNameSpt names))
    (codeEq : target.code = sptFromAList (compileHOL names code))
    (oracleEq : target.compileOracle = Prod.map id (Prod.map (compileHOL names) id) ∘ oracle)
    (noAlloc : ¬target.useAlloc) (noStore : ¬target.useStore) (noStack : ¬target.useStack)
    (run : StackSemEvaluate.evaluate (prog,
      makeInit names (sptFromAList code) oracle { target with clock := fuel }) = (result, post)) :
    ∃ final, StackSemEvaluate.evaluate (progCompHOL names prog, { target with clock := fuel }) =
      (result, final) ∧ final.clock = post.clock ∧ final.ffi = post.ffi := by
  have renamed := compCorrect (c := target.compile) (f := names) prog
    (makeInit names (sptFromAList code) oracle { target with clock := fuel }) result post
    ⟨run, bijective, noAlloc, noStore, noStack, rfl⟩
  have initial := rename_makeInit_eq { target with clock := fuel } names code oracle bijective codeEq oracleEq
  rw [initial] at renamed
  exact ⟨renameState target.compile names post, renamed, rfl, rfl⟩

open Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

/-- The naming stage of the actual full initialization preserves concrete fuel. -/
theorem fullInit_names_same_clock {width : Nat} [NeZero width] {C F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (target : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (prog : HolProg width) (fuel : Nat) (result : Option (StackSemResult width))
    (post : StackSemStateFiniteExact width C F)
    (initialized : Assumptions stackConf dataConf maxHeap sp offset bitmaps code target saveRegs dataSp oracle)
    (run : StackSemEvaluate.evaluate (prog,
      { s2 stackConf dataConf maxHeap sp offset code target saveRegs oracle with clock := fuel }) = (result, post)) :
    ∃ final, StackSemEvaluate.evaluate (progCompHOL stackConf.regNames prog,
      { s3 stackConf dataConf maxHeap sp offset code target saveRegs oracle with clock := fuel }) =
        (result, final) ∧ final.clock = post.clock ∧ final.ffi = post.ffi := by
  have bijective := initialized.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  exact initialized_evaluate_same_clock
    (s3 stackConf dataConf maxHeap sp offset code target saveRegs oracle) stackConf.regNames
    (code2 stackConf dataConf maxHeap sp offset code) (coracle2 stackConf sp offset oracle)
    prog fuel result post bijective rfl rfl (by simp [s3, StackToLab.Proofs.MakeInit.makeInit])
    (by simp [s3, StackToLab.Proofs.MakeInit.makeInit])
    (by simp [s3, StackToLab.Proofs.MakeInit.makeInit]) run

#print axioms fullInit_names_same_clock

#print axioms rename_makeInit_eq
#print axioms initialized_evaluate_same_clock
end InitECandidate.Runtime.StackNames
