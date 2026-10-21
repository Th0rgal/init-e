import InitECandidate.Runtime.WordEntryExecutedCost
import InitECandidate.Runtime.StackExecutionEligibility
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.Asm
open InitECandidate.Runtime.StackToLab

/-- A source final-FFI execution produces a genuinely terminal target
result. The compiler's original resource-failure alternative is retained. -/
theorem compCorrectResult_finalFFI_terminal {F : Type}
    (ac : AsmConfigExact 64) (k frame payload : Nat)
    (source sourcePost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (targetPost : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (event : HolFinalEvent) (output : Option (StackSemResult 64)) (lens : List Nat)
    (contract : compCorrectResult ac k frame payload source sourcePost targetPost
      (some (.finalFfi event)) output lens) :
    ∃ result outcome, output = some result ∧
      executionKindOfResult (some result) = .terminal result outcome := by
  by_cases same : (some (WordSemResult.finalFfi event)).map compileResult = output
  · have eq : output = some (.finalFFI event) := by
      simpa only [Option.map_some,compileResult] using same.symm
    exact ⟨.finalFFI event,.ffiOutcome event,eq,rfl⟩
  · unfold compCorrectResult at contract
    rw [if_pos same] at contract
    refine ⟨.halt (.word 2),.resourceLimitHit,contract.1,?_⟩
    simp [executionKindOfResult]

/-- Entry simulation derives its terminal witness from source termination;
no separate target terminal classification or target run is supplied. -/
theorem compCall_finalFFI_refined_cost {F : Type} (ac : AsmConfigExact 64)
    (start : Nat) (source sourcePost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) F)
    (event : HolFinalEvent) (target : StackSemStateFiniteExact 64 LabToTarget.Config F) (lens : List Nat)
    (code : CostSupportedCode source.code) (frames : CodeFramesBounded source.code source.stackSize 92)
    (run : WordSemStateFiniteExact.evaluate (.call none (some start) [0] none) source =
      (some (.finalFfi event),sourcePost))
    (related : stateRel ac 22 0 0 source target lens 0) :
    ∃ extra post result outcome,
      StackSemEvaluate.evaluate (.call none (.inl start) none,{target with clock := target.clock+extra}) =
        (some result,post) ∧
      compCorrectResult ac 22 0 0 source sourcePost post (some (.finalFfi event)) (some result) lens ∧
      executionKindOfResult (some result) = .terminal result outcome ∧
      stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6
        Compiler.Encoders.RiscV.Target.riscvConfig.addrOffset p)
        (.call none (.inl start) none) {target with clock := target.clock+extra} ≤
        FineCost.wordExecutionCost refinedWordLocalPrice (.call none (some start) [0] none) source := by
  obtain ⟨extra,post,output,targetRun,contract,cost⟩ := compCall_refined_execution_cost ac start source
    (some (.finalFfi event)) sourcePost target lens code frames run (by simp) related
  obtain ⟨result,outcome,same,terminal⟩ := compCorrectResult_finalFFI_terminal ac 22 0 0 source sourcePost
    post event output lens contract
  rw [same] at targetRun contract
  exact ⟨extra,post,result,outcome,targetRun,contract,terminal,cost⟩

#print axioms compCorrectResult_finalFFI_terminal
#print axioms compCall_finalFFI_refined_cost
end InitECandidate.Runtime.WordToStack
