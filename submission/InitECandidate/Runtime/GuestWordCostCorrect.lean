import InitECandidate.Runtime.GuestWordCostSupport
import InitECandidate.Runtime.GuestWordInitializationFrames
import InitECandidate.Runtime.WordRefinedLocalPrice
namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open InitECandidate.Proofs.BackendStages InitECandidate.Runtime.FineCost

/-- Concrete allocated guest entry cost: code eligibility, total frame
coverage, the 92-word frame limit, and local compiler prices are discharged
by the actual artifact certificates, uniformly over input state and clock. -/
theorem guest_initialized_word_cost_correct {F : Type}
    (target : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (oracle : Nat → (Nat × LabToTarget.Config) × List (Nat × Nat × WordLangProgHOL (BitVec 64)))
    (start fuel : Nat) :
    let source := Compiler.Backend.WordToStack.Native.Initialization.makeInit riscvConfig 22 target
      (sptFromAList Native.programs0) oracle
    RefinedExecutedSimulation riscvConfig (.call none (some start) [0] none) {source with clock := fuel}
      (wordExecutionCost refinedWordLocalPrice (.call none (some start) [0] none) {source with clock := fuel}) := by
  dsimp only
  apply refinedWordCost_correct riscvConfig _ _ rfl
  · exact guest_word_code_cost_supported
  · exact guest_word_initialization_frames target oracle

#print axioms guest_initialized_word_cost_correct
end InitECandidate.Runtime.WordToStack
