import InitECandidate.Runtime.RawCallEntryExecutedCost
import InitECandidate.Runtime.GuestRawCallFrames
import InitECandidate.Runtime.BaselineRuntimeEntry
import InitECandidate.Proofs.BackendStages.Raw

namespace InitECandidate.Runtime.StackRawCall
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open InitECandidate.Proofs.BackendStages
open InitECandidate.Runtime.StackToLab

/-- Instantiate the whole raw-call cost theorem at the real initialized guest.
All frame eligibility, code coverage, declaration uniqueness and oracle
conditions are derived from checked guest artifacts and initialization. -/
theorem guest_raw_entry_cost (input : Guest.InputBlob) (entry : BaselineRuntimeEntry input)
    (start fuel : Nat) (result : Option (StackSemResult 64))
    (post : StackSemStateFiniteExact 64 LabToTarget.Config Guest.HostMemory)
    (run : StackSemEvaluate.evaluate (.call none (.inl start) none,
      {entryStackState entry.cfg entry.source with clock := fuel}) = (result, post))
    (nonerror : result ≠ some .error) :
    ∃ extra final,
      StackSemEvaluate.evaluate (.call none (.inl start) none,
        {entryStackState entry.cfg entry.source with
          code := sptFromAList (StackRawCall.compile Native.stack)
          clock := fuel + extra}) = (result, final) ∧ final.ffi = post.ffi ∧
      stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
        (.call none (.inl start) none)
        {entryStackState entry.cfg entry.source with
          code := sptFromAList (StackRawCall.compile Native.stack)
          clock := fuel + extra} ≤
      stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
        (.call none (.inl start) none) {entryStackState entry.cfg entry.source with clock := fuel} := by
  have distinct : (Native.stack.map Prod.fst).Nodup := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, good, -, -, -, -, -, -, -, -, -⟩ := id entry.stackAssumptions
    exact good.1
  exact entrySimulation_executed riscvConfig.addrOffset Native.stack
    (entryStackState entry.cfg entry.source) start fuel result post distinct rfl
    guest_raw_call_frames (by intro index; rfl) run nonerror

#print axioms guest_raw_entry_cost
end InitECandidate.Runtime.StackRawCall
