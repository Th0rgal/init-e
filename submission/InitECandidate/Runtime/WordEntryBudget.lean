import InitECandidate.Runtime.WordWorkCorrect
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompCall
import Flapjack.Compiler.Backend.WordToStack.Proofs.SemanticsHelpers
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.WordToStackProofs.CompCall
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native

theorem compCall_bounded {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) :
    ∀ (start : Nat) (s : WordSemStateFiniteExact width (Nat × C) F) (k : Nat)
      (res : Option (WordSemResult width)) (s1 : WordSemStateFiniteExact width (Nat × C) F)
      (t : StackSemStateFiniteExact width C F) (lens : List Nat),
      WordSemStateFiniteExact.evaluate (.call none (some start) [0] none) s = (res, s1) ∧
      res ≠ some .error ∧ stateRel ac k 0 0 s t lens 0 →
      ∃ (ck : Nat), ck ≤ wordWork (.call none (some start) [0] none) s ∧ ∃ (t1 : StackSemStateFiniteExact width C F) (res1 : Option (StackSemResult width)),
        StackSemEvaluate.evaluate (.call none (.inl start) none, {t with clock := t.clock + ck}) =
          (res1, t1) ∧ (1 : BitVec width) ≠ 0 ∧ (2 : BitVec width) ≠ 0 ∧
        (open Classical in if res.map compileResult = res1 then s1.ffi = t1.ffi ∧ s1.clock = t1.clock
         else res1 = some (.halt (.word 2)) ∧ List.IsPrefix t1.ffi.ioEvents s1.ffi.ioEvents ∧
           s1.stackMax.getD (s1.stackLimit + 1) > s1.stackLimit) := by
  intro start s k res s1 t lens ⟨run, notError, related⟩
  have kBound : 4 < k := related.2.2.2.2.2.2.2.2.2.1
  obtain ⟨ck, bound, t1, res1, targetRun, resultRel⟩ :=
    wordWork_correct ac (.call none (some start) [0] none) s k 0 0 s1 t res
      .nil .nil t.bitmaps.length t.bitmaps.length (.seq .skip (.call none (.inl start) none)) lens
      ⟨run, notError, related, by simp [postAllocConventionsHOL, everyVarHOL, everyStackVarHOL, callArgConventionHOL, isPhyVar], by simp [flatExpConventions], by
        simp [compNative, callDestNative, seqStackFreeNative, Compiler.Backend.WordToStack.stackFree],
        by simp [appListAppend, appendAux], by simp [appListAppend, appendAux], by simp [appListAppend, appendAux],
        by simp [StackSem.getLabelsExact], by simp [maxVarHOL, maxList]; omega⟩
  have wide : 8 ≤ width := by
    unfold stateRel at related
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,h,_⟩ := related
    exact h
  have oneLt : 1 < 2 ^ width := Nat.one_lt_two_pow (by omega)
  have twoLt : 2 < 2 ^ width :=
    calc 2 < 2 ^ 8 := by norm_num
      _ ≤ 2 ^ width := Nat.pow_le_pow_right (by norm_num) wide
  refine ⟨ck, bound, t1, res1, (evaluateSeqSkip _ _).symm.trans targetRun, ?_, ?_, ?_⟩
  · intro h
    have := congrArg BitVec.toNat h
    simp [Nat.mod_eq_of_lt oneLt] at this
  · intro h
    have := congrArg BitVec.toNat h
    simp [Nat.mod_eq_of_lt twoLt] at this
  · unfold compCorrectResult at resultRel
    by_cases same : res.map compileResult = res1
    · rw [if_pos same]
      rw [if_neg (not_not.mpr same)] at resultRel
      have ffiClock : ∀ {f frame lens' extra} {s' : WordSemStateFiniteExact width (Nat × C) F},
          stateRel ac k f frame s' t1 lens' extra → s'.ffi = t1.ffi ∧ s'.clock = t1.clock :=
        fun rel => ⟨rel.2.2.2.1.symm, rel.1⟩
      rcases res with _ | r
      · exact ffiClock resultRel
      · cases r with
        | result _ values => exact ffiClock resultRel.1
        | exception _ value =>
          obtain ⟨nonGc, gc, rel, _, _⟩ := resultRel
          exact ffiClock (s' := pushLocals nonGc gc s1) rel
        | «break» _ => exact ffiClock resultRel
        | «continue» _ => exact ffiClock resultRel
        | _ => exact resultRel
    · rw [if_neg same]
      rw [if_pos same] at resultRel
      exact resultRel


/-- Clock-indexed entry execution with the complete result/resource alternative
and a concrete upper bound on initial target fuel. -/
theorem entrySimulation_bounded {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat) (start fuel : Nat)
    (result : Option (WordSemResult width)) (post : WordSemStateFiniteExact width (Nat × C) F)
    (related : stateRel ac k 0 0 source target lens 0)
    (run : WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      {source with clock := fuel} = (result, post))
    (notError : result ≠ some .error) :
    ∃ targetFuel targetResult final,
      targetFuel ≤ fuel + wordWork (.call none (some start) [0] none) {source with clock := fuel} ∧
      StackSemEvaluate.evaluate (.call none (.inl start) none, {target with clock := targetFuel}) =
        (targetResult, final) ∧
      ((result.map compileResult = targetResult ∧ post.ffi = final.ffi ∧ post.clock = final.clock) ∨
        (result.map compileResult ≠ targetResult ∧ targetResult = some (.halt (.word 2)) ∧
          List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          post.stackMax.getD (post.stackLimit + 1) > post.stackLimit)) := by
  have moved := SemanticsHelpers.stateRelWithClock ac k fuel source target lens 0 related
  obtain ⟨extra, bound, final, targetResult, targetRun, _, _, outcome⟩ :=
    compCall_bounded ac start {source with clock := fuel} k result post
      {target with clock := fuel} lens ⟨run, notError, moved⟩
  refine ⟨fuel + extra, targetResult, final, by omega, targetRun, ?_⟩
  by_cases same : result.map compileResult = targetResult
  · rw [if_pos same] at outcome
    exact Or.inl ⟨same, outcome⟩
  · rw [if_neg same] at outcome
    exact Or.inr ⟨same, outcome⟩

/-- Retains the nonzero resource words needed to distinguish rejection from success
when composing the entry bound with later compiler stages. -/
theorem entrySimulation_with_resource_words_bounded {width : Nat} [NeZero width] {C F : Type}
    (ac : AsmConfigExact width) (k : Nat)
    (source : WordSemStateFiniteExact width (Nat × C) F)
    (target : StackSemStateFiniteExact width C F) (lens : List Nat) (start fuel : Nat)
    (result : Option (WordSemResult width)) (post : WordSemStateFiniteExact width (Nat × C) F)
    (related : stateRel ac k 0 0 source target lens 0)
    (run : WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      {source with clock := fuel} = (result, post))
    (notError : result ≠ some .error) :
    ∃ targetFuel targetResult final,
      targetFuel ≤ fuel + wordWork (.call none (some start) [0] none) {source with clock := fuel} ∧
      StackSemEvaluate.evaluate (.call none (.inl start) none, {target with clock := targetFuel}) =
        (targetResult, final) ∧
      (1 : BitVec width) ≠ 0 ∧ (2 : BitVec width) ≠ 0 ∧
      ((result.map compileResult = targetResult ∧ post.ffi = final.ffi ∧ post.clock = final.clock) ∨
        (result.map compileResult ≠ targetResult ∧ targetResult = some (.halt (.word 2)) ∧
          List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          post.stackMax.getD (post.stackLimit + 1) > post.stackLimit)) := by
  have moved := SemanticsHelpers.stateRelWithClock ac k fuel source target lens 0 related
  obtain ⟨extra, bound, final, targetResult, targetRun, oneNe, twoNe, outcome⟩ :=
    compCall_bounded ac start {source with clock := fuel} k result post
      {target with clock := fuel} lens ⟨run, notError, moved⟩
  refine ⟨fuel + extra, targetResult, final, by omega, targetRun, oneNe, twoNe, ?_⟩
  by_cases same : result.map compileResult = targetResult
  · rw [if_pos same] at outcome
    exact Or.inl ⟨same, outcome⟩
  · rw [if_neg same] at outcome
    exact Or.inr ⟨same, outcome⟩

#print axioms entrySimulation_with_resource_words_bounded

#print axioms entrySimulation_bounded
#print axioms compCall_bounded
end InitECandidate.Runtime.WordToStack
