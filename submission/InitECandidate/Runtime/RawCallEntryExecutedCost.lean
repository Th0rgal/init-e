import InitECandidate.Runtime.RawCallExecutedCorrect
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompileSemantics

namespace InitECandidate.Runtime.StackRawCall
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRawCall Flapjack.Compiler.Backend.StackRawCall.CompileSemantics
open InitECandidate.Runtime.StackToLab

/-- Whole-program entry transfer for the actual raw-call compiler. The same
witness supplies both the evaluator run and its executed-cost bound. -/
theorem entrySimulation_executed {F : Type} (bounds : BitVec 64 × BitVec 64)
    (code : List (Nat × HolProg 64))
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (start fuel : Nat) (result : Option (StackSemResult 64))
    (post : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (distinct : (code.map Prod.fst).Nodup) (sourceCode : source.code = sptFromAList code)
    (eligible : rawCallCodeFramesSupported code = true) (oracle : EmptyInstallOracle source)
    (run : StackSemEvaluate.evaluate (.call none (.inl start) none, {source with clock := fuel}) =
      (result, post)) (nonerror : result ≠ some .error) :
    ∃ extra final,
      StackSemEvaluate.evaluate (.call none (.inl start) none,
        {source with code := sptFromAList (compile code), clock := fuel + extra}) =
        (result, final) ∧ final.ffi = post.ffi ∧
      stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 bounds p)
        (.call none (.inl start) none)
        {source with code := sptFromAList (compile code), clock := fuel + extra} ≤
      stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 bounds p)
        (.call none (.inl start) none) {source with clock := fuel} := by
  have relation := initialRelation code {source with clock := fuel} distinct sourceCode
  have global : RawCallFramesSupportedCode source.code := by
    rw [sourceCode]
    exact RawCallFramesSupportedCode.of_list code eligible
  obtain ⟨extra, final, space, postRelation, targetRun, guard, cost⟩ :=
    (rawCall_cost_correct bounds (.call none (.inl start) none) {source with clock := fuel}
      (by simp [rawCallFramesSupported]) global oracle (collectInfo code .ln)
      {source with clock := fuel, code := sptFromAList (compile code)} post result
      ⟨run, nonerror, relation⟩).2
  refine ⟨extra, {final with stackSpace := space}, ?_, ?_, ?_⟩
  · simpa only [comp] using targetRun
  · obtain ⟨_, _, equality, _⟩ := postRelation
    subst final
    rfl
  · simpa only [comp] using cost

#print axioms entrySimulation_executed
end InitECandidate.Runtime.StackRawCall
