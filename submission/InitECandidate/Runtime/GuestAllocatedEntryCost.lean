import InitECandidate.Runtime.FullAllocationExecutedCost
import InitECandidate.Runtime.ActualAllocationFree
import InitECandidate.Runtime.GuestRawCallEntryCost

namespace InitECandidate.Runtime.StackAlloc
open InitE
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics
open InitECandidate.Proofs.BackendStages
open InitECandidate.Runtime.StackToLab

/-- The actual guest allocation boundary. The code/oracle syntax, selected
initializer flags and bounds, and Raw compilation identity are all discharged
from the checked artifacts. Only the actual non-error Raw entry run is input. -/
theorem guest_allocated_entry_cost (input : Guest.InputBlob) (entry : BaselineRuntimeEntry input)
    (price : HolProg 64 → Nat) (start fuel : Nat) (result : Option (StackSemResult 64))
    (post : StackSemStateFiniteExact 64 LabToTarget.Config Guest.HostMemory)
    (run : StackSemEvaluate.evaluate (.call none (.inl start) none,
      {entryStackState entry.cfg entry.source with code := sptFromAList Raw.stack, clock := fuel}) = (result, post))
    (safe : result ≠ some .error) :
    ∃ final,
      StackSemEvaluate.evaluate (.call none (.inl start) none,
        {entry.source with clock := fuel}) = (result, final) ∧ final.ffi = post.ffi ∧
      stackExecutionCost (fun p _ => price p) (.call none (.inl start) none)
          {entry.source with clock := fuel} ≤
        stackExecutionCost (fun p _ => price p) (.call none (.inl start) none)
          {entryStackState entry.cfg entry.source with code := sptFromAList Raw.stack, clock := fuel} := by
  have free : allocationFreeCode (StackRawCall.compile Native.stack) = true := by
    rw [Raw.compile_eq]
    exact actual_allocationFree
  have oracleFree : ∀ n, allocationFreeCode (entryStackOracle entry.cfg n).2.1 = true := by
    intro n
    rfl
  have rawRun : StackSemEvaluate.evaluate (.call none (.inl start) none,
      Flapjack.Compiler.Backend.StackAlloc.makeInit baselineCompilerConfig.dataConf
        (sptFromAList (StackRawCall.compile Native.stack)) (entryStackOracle entry.cfg)
        {entry.source with clock := fuel}) = (result, post) := by
    rw [Raw.compile_eq]
    exact run
  have rawStateEq : Flapjack.Compiler.Backend.StackAlloc.makeInit baselineCompilerConfig.dataConf
      (sptFromAList Raw.stack) (entryStackOracle entry.cfg) {entry.source with clock := fuel} =
      {entryStackState entry.cfg entry.source with code := sptFromAList Raw.stack, clock := fuel} := rfl
  obtain ⟨final, evaluated, ffi, cost⟩ := before_alloc_entry_executed_cost price
    baselineCompilerConfig.stackConf baselineCompilerConfig.dataConf entryHeapLimit entrySp
    riscvConfig.addrOffset InitECandidate.bitmaps Native.stack
    (LabToTarget.baselineLabState input entry.cfg entry.asm entry.memory entry.bitmapDomain entry.sharedDomain)
    entrySaveRegs 0 (entryStackOracle entry.cfg) entry.source post fuel start result
    entry.stackAssumptions entry.selection free oracleFree rawRun safe
  rw [Raw.compile_eq, rawStateEq] at cost
  exact ⟨final, evaluated, ffi, cost⟩

/-- Compose actual raw-call lowering and allocation lowering without an
extra clock factor, preserving the real selected state's output and FFI. -/
theorem guest_raw_allocated_entry_cost (input : Guest.InputBlob) (entry : BaselineRuntimeEntry input)
    (start fuel : Nat) (result : Option (StackSemResult 64))
    (post : StackSemStateFiniteExact 64 LabToTarget.Config Guest.HostMemory)
    (run : StackSemEvaluate.evaluate (.call none (.inl start) none,
      {entryStackState entry.cfg entry.source with clock := fuel}) = (result, post))
    (safe : result ≠ some .error) :
    ∃ extra final,
      StackSemEvaluate.evaluate (.call none (.inl start) none,
        {entry.source with clock := fuel + extra}) = (result, final) ∧ final.ffi = post.ffi ∧
      stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
          (.call none (.inl start) none) {entry.source with clock := fuel + extra} ≤
        stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 riscvConfig.addrOffset p)
          (.call none (.inl start) none) {entryStackState entry.cfg entry.source with clock := fuel} := by
  obtain ⟨extra, rawPost, rawRun, rawFfi, rawCost⟩ :=
    StackRawCall.guest_raw_entry_cost input entry start fuel result post run safe
  obtain ⟨final, targetRun, allocationFfi, allocationCost⟩ := guest_allocated_entry_cost input entry
    (refinedRemovalLocalPrice 6 riscvConfig.addrOffset) start (fuel + extra) result rawPost rawRun safe
  exact ⟨extra, final, targetRun, allocationFfi.trans rawFfi, allocationCost.trans rawCost⟩

#print axioms guest_allocated_entry_cost
#print axioms guest_raw_allocated_entry_cost
end InitECandidate.Runtime.StackAlloc
