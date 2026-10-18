import InitECandidate.Runtime.WordInitializedBudget
import InitECandidate.Runtime.WordEntryPathBudget
import Flapjack.Compiler.Backend.WordToStack.Proofs.CompileSemantics
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.WordToStackProofs
open Flapjack.Compiler.Encoders.Asm Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.WordToStack.Native
open Flapjack.Compiler.Backend.WordToStack.Native.Initialization
open Flapjack.WordToStackProofs.InitializationStateRel

theorem initialized_entry_path_bounded {width : Nat} [NeZero width] {C F : Type}
    (asmConf : AsmConfigExact width) (code : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (t : StackSemStateFiniteExact width C F) (k : Nat)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (h : InitializationPremises asmConf code t k coracle)
    (start fuel : Nat) (result : Option (WordSemResult width))
    (post : WordSemStateFiniteExact width (Nat × C) F)
    (run : WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      {makeInit asmConf k t (sptFromAList code) coracle with clock := fuel} = (result, post))
    (notError : result ≠ some .error) :
    ∃ targetFuel targetResult final,
      targetFuel ≤ fuel + wordPathWork (.call none (some start) [0] none)
        {makeInit asmConf k t (sptFromAList code) coracle with clock := fuel} ∧
      StackSemEvaluate.evaluate (.call none (.inl start) none, {t with clock := targetFuel}) =
        (targetResult, final) ∧
      ((result.map Flapjack.WordToStackProofs.CompCorrect.compileResult = targetResult ∧ post.ffi = final.ffi ∧ post.clock = final.clock) ∨
        (result.map Flapjack.WordToStackProofs.CompCorrect.compileResult ≠ targetResult ∧ targetResult = some (.halt (.word 2)) ∧
          List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          post.stackMax.getD (post.stackLimit + 1) > post.stackLimit)) := by
  exact entrySimulation_path_bounded asmConf k (makeInit asmConf k t (sptFromAList code) coracle)
    t [] start fuel result post (initialized_relation asmConf code t k coracle h) run notError

/-- Initialized entry transfer retaining the rejection-word discrimination facts. -/
theorem initialized_entry_with_resource_words_path_bounded {width : Nat} [NeZero width] {C F : Type}
    (asmConf : AsmConfigExact width) (code : List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (t : StackSemStateFiniteExact width C F) (k : Nat)
    (coracle : Nat → (Nat × C) × List (Nat × Nat × WordLangProgHOL (BitVec width)))
    (h : InitializationPremises asmConf code t k coracle)
    (start fuel : Nat) (result : Option (WordSemResult width))
    (post : WordSemStateFiniteExact width (Nat × C) F)
    (run : WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      {makeInit asmConf k t (sptFromAList code) coracle with clock := fuel} = (result, post))
    (notError : result ≠ some .error) :
    ∃ targetFuel targetResult final,
      targetFuel ≤ fuel + wordPathWork (.call none (some start) [0] none)
        {makeInit asmConf k t (sptFromAList code) coracle with clock := fuel} ∧
      StackSemEvaluate.evaluate (.call none (.inl start) none, {t with clock := targetFuel}) =
        (targetResult, final) ∧
      (1 : BitVec width) ≠ 0 ∧ (2 : BitVec width) ≠ 0 ∧
      ((result.map Flapjack.WordToStackProofs.CompCorrect.compileResult = targetResult ∧ post.ffi = final.ffi ∧ post.clock = final.clock) ∨
        (result.map Flapjack.WordToStackProofs.CompCorrect.compileResult ≠ targetResult ∧ targetResult = some (.halt (.word 2)) ∧
          List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          post.stackMax.getD (post.stackLimit + 1) > post.stackLimit)) := by
  exact entrySimulation_with_resource_words_path_bounded asmConf k (makeInit asmConf k t (sptFromAList code) coracle)
    t [] start fuel result post (initialized_relation asmConf code t k coracle h) run notError

#print axioms initialized_entry_with_resource_words_path_bounded

#print axioms initialized_entry_path_bounded
end InitECandidate.Runtime.WordToStack
