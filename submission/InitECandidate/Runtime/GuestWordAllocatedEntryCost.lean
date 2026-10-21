import InitECandidate.Runtime.GuestAllocatedEntryCost
import InitECandidate.Runtime.GuestWordCostCorrect
import InitECandidate.Runtime.WordEntryTerminalResult
import InitECandidate.Runtime.WordInitializedBudget

namespace InitECandidate.Runtime.WordToStack
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.WordToStackProofs Flapjack.WordToStackProofs.CompCorrect
open InitECandidate.Proofs.BackendStages
open InitECandidate.Runtime.FineCost InitECandidate.Runtime.StackToLab

/-- The concrete allocated Word guest entry reaches the selected physical
Stack initializer through Word-to-Stack, raw-call and allocation lowering.
All three executed-cost comparisons compose with coefficient one. The source
final-FFI premise derives a terminal target, retaining the compiler's original
resource-limit alternative. -/
theorem guest_word_allocated_entry_cost (input : Guest.InputBlob) (entry : BaselineRuntimeEntry input)
    (start fuel : Nat) (event : HolFinalEvent)
    (sourcePost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory)
    (run : WordSemStateFiniteExact.evaluate (.call none (some start) [0] none)
      {entryWordState entry.cfg entry.source with clock := fuel} = (some (.finalFfi event), sourcePost)) :
    ∃ extra final result outcome,
      StackSemEvaluate.evaluate (.call none (.inl start) none,
        {entry.source with clock := fuel + extra}) = (some result, final) ∧
      executionKindOfResult (some result) = .terminal result outcome ∧
      stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
          (.call none (.inl start) none) {entry.source with clock := fuel + extra} ≤
        wordExecutionCost refinedWordLocalPrice (.call none (some start) [0] none)
          {entryWordState entry.cfg entry.source with clock := fuel} := by
  let target := {entryStackState entry.cfg entry.source with clock := fuel}
  have initialized : InitializationPremises riscvConfig Native.programs0 target 22
      (entryWordOracle entry.cfg) := entry.wordInitialized
  have related : stateRel riscvConfig 22 0 0
      {entryWordState entry.cfg entry.source with clock := fuel} target [] 0 :=
    initialized_relation riscvConfig Native.programs0 target 22 (entryWordOracle entry.cfg) initialized
  have supported : CostSupportedCode
      ({entryWordState entry.cfg entry.source with clock := fuel}).code := guest_word_code_cost_supported
  have frames : CodeFramesBounded
      ({entryWordState entry.cfg entry.source with clock := fuel}).code
      ({entryWordState entry.cfg entry.source with clock := fuel}).stackSize 92 :=
    guest_word_initialization_frames target (entryWordOracle entry.cfg)
  obtain ⟨extra1, stackPost, result, outcome, stackRun, contract, terminal, wordCost⟩ :=
    compCall_finalFFI_refined_cost riscvConfig start
      {entryWordState entry.cfg entry.source with clock := fuel} sourcePost event target []
      supported frames run related
  have stackRun' : StackSemEvaluate.evaluate (.call none (.inl start) none,
      {entryStackState entry.cfg entry.source with clock := fuel + extra1}) =
        (some result, stackPost) := stackRun
  have nonerror : some result ≠ some (StackSemResult.error : StackSemResult 64) := by
    intro bad
    have equal : result = .error := Option.some.inj bad
    subst result
    simp only [executionKindOfResult] at terminal
    cases terminal
  obtain ⟨extra2, final, finalRun, ffi, allocationCost⟩ :=
    StackAlloc.guest_raw_allocated_entry_cost input entry start (fuel + extra1)
      (some result) stackPost stackRun' nonerror
  refine ⟨extra1 + extra2, final, result, outcome, ?_, terminal, ?_⟩
  · simpa only [Nat.add_assoc] using finalRun
  · have total := allocationCost.trans wordCost
    simpa only [target, Nat.add_assoc] using total

#print axioms guest_word_allocated_entry_cost
end InitECandidate.Runtime.WordToStack
