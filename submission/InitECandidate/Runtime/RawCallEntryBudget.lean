import InitECandidate.Runtime.RawCallCorrectBudget
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompileSemantics
namespace InitECandidate.Runtime.StackRawCall
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.CompileSemantics

/-- Whole-program entry simulation retaining its actual extra-clock ceiling. -/
theorem entrySimulation_bounded {width : Nat} [NeZero width] {C F : Type}
    (code : List (Nat × HolProg width)) (source : StackSemStateFiniteExact width C F)
    (start clock : Nat) (result : Option (StackSemResult width))
    (post : StackSemStateFiniteExact width C F)
    (distinct : (code.map Prod.fst).Nodup) (sourceCode : source.code = sptFromAList code)
    (run : StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width), {source with clock := clock}) =
      (result, post)) (nonError : result ≠ some .error) :
    ∃ extra, extra ≤ clock - post.clock - 1 ∧ ∃ targetPost, StackSemEvaluate.evaluate
      ((.call none (.inl start) none : HolProg width),
        {source with code := sptFromAList (compile code), clock := clock + extra}) =
      (result, targetPost) ∧ targetPost.ffi = post.ffi := by
  have relation := initialRelation code {source with clock := clock} distinct sourceCode
  obtain ⟨extra, extraBound, targetPost, space, postRelation, targetRun, _⟩ :=
    (compCorrect_bounded (.call none (.inl start) none)
      {source with clock := clock}
      {source with clock := clock, code := sptFromAList (compile code)}
      post (collectInfo code .ln) result ⟨run, nonError, relation⟩).2
  refine ⟨extra, extraBound, {targetPost with stackSpace := space}, ?_, ?_⟩
  · simpa only [comp] using targetRun
  · obtain ⟨_, _, equality, _⟩ := postRelation
    subst targetPost
    rfl


/-- A uniform linear fuel transfer for the complete RawCall pass. -/
theorem entrySimulation_twice {width : Nat} [NeZero width] {C F : Type}
    (code : List (Nat × HolProg width)) (source : StackSemStateFiniteExact width C F)
    (start fuel : Nat) (result : Option (StackSemResult width))
    (post : StackSemStateFiniteExact width C F)
    (distinct : (code.map Prod.fst).Nodup) (sourceCode : source.code = sptFromAList code)
    (run : StackSemEvaluate.evaluate (.call none (.inl start) none, {source with clock := fuel}) =
      (result, post)) (nonError : result ≠ some .error) :
    ∃ targetFuel final, targetFuel ≤ 2 * fuel ∧ StackSemEvaluate.evaluate
      (.call none (.inl start) none,
        {source with code := sptFromAList (compile code), clock := targetFuel}) =
        (result, final) ∧ final.ffi = post.ffi := by
  obtain ⟨extra, bound, final, evaluated, ffi⟩ :=
    entrySimulation_bounded code source start fuel result post distinct sourceCode run nonError
  exact ⟨fuel + extra, final, by omega, evaluated, ffi⟩

#print axioms entrySimulation_twice
end InitECandidate.Runtime.StackRawCall
