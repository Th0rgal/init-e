import InitECandidate.Runtime.StackRefinedRemovalPrice
import InitECandidate.Runtime.StackExecutionCost
import Flapjack.Compiler.Backend.StackRawCall.Proofs.CompCorrect.Seq.Optimized

namespace InitECandidate.Runtime.StackRawCall
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Backend.StackLang
open InitECandidate.Runtime.StackToLab

/-- The local operations introduced by the actual raw-tail-call optimizer.
The recursive callee body is deliberately excluded: its execution must be
related separately by the whole-pass induction. -/
noncomputable def optimizedTailLocalCost (bounds : BitVec 64 × BitVec 64)
    (released allocated dest : Nat) : Nat :=
  let price := refinedRemovalLocalPrice 6 bounds
  if allocated = released then price (.rawCall dest)
  else if allocated < released then
    price (.stackFree (released - allocated)) + price (.rawCall dest)
  else price .tick + price (.stackAlloc (allocated - released)) + price (.rawCall dest)

/-- Nonzero releases fund even the extra tick in the growing-frame case.
This is a local compiler-price inequality, not an assumed bound on the
optimized execution. Both frame bounds cover the actual guest's 92 slots. -/
theorem optimizedTailLocalCost_le (bounds : BitVec 64 × BitVec 64)
    (released allocated dest : Nat) (positive : 0 < released)
    (releaseBound : released ≤ 255) (allocationBound : allocated ≤ 255) :
    optimizedTailLocalCost bounds released allocated dest ≤
      refinedRemovalLocalPrice 6 bounds (.stackFree released) +
      refinedRemovalLocalPrice 6 bounds (.call none (.inl dest) none) +
      refinedRemovalLocalPrice 6 bounds (.stackAlloc allocated) := by
  have releasedChunks : (released + 254) / 255 = 1 := by omega
  have allocatedChunks : (allocated + 254) / 255 ≤ 1 := by omega
  have freeChunks : (released - allocated + 254) / 255 ≤ 1 := by omega
  have allocChunks : (allocated - released + 254) / 255 ≤ 1 := by omega
  simp only [optimizedTailLocalCost, refinedRemovalLocalPrice,
    refinedNativePriceWithGap, removalLocalPrice, nativePriceWithGap,
    callJumpWork, instLocalCost, releasedChunks]
  split_ifs <;> omega

#print axioms optimizedTailLocalCost_le

/-- The cost recurrence for the real successful direct-call entry. The body
cost is measured in its actual post-allocation state, including clock use. -/
theorem callAlloc_executionCost {F : Type} (bounds : BitVec 64 × BitVec 64)
    (dest allocated : Nat) (body : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (entry : sptLookup dest source.code = some (.seq (.stackAlloc allocated) body))
    (enabled : source.useStack = true) (nonzero : source.clock ≠ 0)
    (space : allocated ≤ source.stackSpace) :
    stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 bounds p)
        (.call none (.inl dest) none) source =
      refinedRemovalLocalPrice 6 bounds (.call none (.inl dest) none) +
      refinedRemovalLocalPrice 6 bounds (.stackAlloc allocated) +
      stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 bounds p) body
        {Flapjack.StackSemStateOps.decClock source with
          stackSpace := source.stackSpace - allocated} := by
  rw [stackExecutionCost]
  simp only [Option.isSome_none, Bool.false_eq_true, nonzero, if_false,
    Flapjack.StackSemControl.findCode, entry]
  have allocationRun : Flapjack.StackSemEvaluate.evaluate
      (.stackAlloc allocated, Flapjack.StackSemStateOps.decClock source) =
      (none, {Flapjack.StackSemStateOps.decClock source with
        stackSpace := source.stackSpace - allocated}) := by
    simp [Flapjack.StackSemEvaluate.evaluate_stackAlloc,
      Flapjack.StackSemStateOps.decClock, enabled, Nat.not_lt.mpr space]
  rw [stackExecutionCost]
  rw [allocationRun]
  simp [stackExecutionCost, Flapjack.StackSemStateOps.decClock,
    Flapjack.StackSemControl.fixClock, refinedRemovalLocalPrice,
    removalLocalPrice, nativePriceWithGap, Nat.add_assoc]

#print axioms callAlloc_executionCost

/-- Exact executed cost of the successful optimized entry. This uses the
actual evaluator and its extra clock, not an independently assumed target
budget. The callee counter remains explicit for the recursive code relation. -/
theorem optimizedTail_executionCost {F : Type} (bounds : BitVec 64 × BitVec 64)
    (released allocated dest : Nat) (body : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (entry : sptLookup dest source.code = some (.seq (.stackAlloc allocated) body))
    (enabled : source.useStack = true) (nonzero : source.clock ≠ 0)
    (releaseSafe : source.stackSpace + released ≤ source.stack.length)
    (space : allocated ≤ source.stackSpace + released) :
    stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 bounds p)
      (StackRawCall.SeqCase.optimizedSeq released allocated dest)
      {source with clock := source.clock + (if released < allocated then 1 else 0)} =
      optimizedTailLocalCost bounds released allocated dest +
      stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 bounds p) body
        {Flapjack.StackSemStateOps.decClock source with
          stackSpace := source.stackSpace + released - allocated} := by
  by_cases equal : allocated = released
  · subst allocated
    simp [StackRawCall.SeqCase.optimizedSeq, optimizedTailLocalCost,
      stackExecutionCost, nonzero, entry, Flapjack.StackSemStateOps.decClock]
  · by_cases less : allocated < released
    · have safe : ¬ source.stack.length < source.stackSpace + (released - allocated) := by omega
      have safeFinal : ¬ source.stack.length < source.stackSpace + released - allocated := by omega
      have finalSpace : source.stackSpace + (released - allocated) =
          source.stackSpace + released - allocated := by omega
      simp [StackRawCall.SeqCase.optimizedSeq, optimizedTailLocalCost, equal, less,
        show ¬ released < allocated by omega, stackExecutionCost,
        Flapjack.StackSemEvaluate.evaluate_stackFree, enabled, safe, safeFinal, nonzero,
        entry, Flapjack.StackSemControl.fixClock, Flapjack.StackSemStateOps.decClock,
        finalSpace, refinedRemovalLocalPrice, removalLocalPrice, nativePriceWithGap,
        Nat.add_assoc]
    · have greater : released < allocated := by omega
      have safe : ¬ source.stackSpace < allocated - released := by omega
      have finalSpace : source.stackSpace - (allocated - released) =
          source.stackSpace + released - allocated := by omega
      simp [StackRawCall.SeqCase.optimizedSeq, optimizedTailLocalCost, equal, less,
        greater, stackExecutionCost, Flapjack.StackSemEvaluate.evaluate_tick,
        Flapjack.StackSemEvaluate.evaluate_stackAlloc, enabled, safe, nonzero,
        entry, Flapjack.StackSemControl.fixClock, Flapjack.StackSemStateOps.decClock,
        finalSpace, refinedRemovalLocalPrice, refinedNativePriceWithGap,
        removalLocalPrice, nativePriceWithGap, Nat.add_assoc]

#print axioms optimizedTail_executionCost

/-- Actual successful tail-entry optimization does not increase the refined
execution counter when the removed release is nonzero. Callee code is the
same on both sides here; whole-pass transport must separately compare the
original body with its recursively compiled body. -/
theorem optimizedTail_executionCost_le {F : Type} (bounds : BitVec 64 × BitVec 64)
    (released allocated dest : Nat) (body : HolProg 64)
    (source : StackSemStateFiniteExact 64 LabToTarget.Config F)
    (entry : sptLookup dest source.code = some (.seq (.stackAlloc allocated) body))
    (enabled : source.useStack = true) (nonzero : source.clock ≠ 0)
    (releaseSafe : source.stackSpace + released ≤ source.stack.length)
    (space : allocated ≤ source.stackSpace + released)
    (positive : 0 < released) (releaseBound : released ≤ 255)
    (allocationBound : allocated ≤ 255) :
    stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 bounds p)
      (StackRawCall.SeqCase.optimizedSeq released allocated dest)
      {source with clock := source.clock + (if released < allocated then 1 else 0)} ≤
    stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 bounds p)
      (.seq (.stackFree released) (.call none (.inl dest) none)) source := by
  rw [optimizedTail_executionCost bounds released allocated dest body source entry
    enabled nonzero releaseSafe space]
  have releaseRun : Flapjack.StackSemEvaluate.evaluate (.stackFree released, source) =
      (none, {source with stackSpace := source.stackSpace + released}) := by
    simp [Flapjack.StackSemEvaluate.evaluate_stackFree, enabled,
      Nat.not_lt.mpr releaseSafe]
  have callCost := callAlloc_executionCost bounds dest allocated body
    {source with stackSpace := source.stackSpace + released} entry enabled nonzero space
  have localBound := optimizedTailLocalCost_le bounds released allocated dest
    positive releaseBound allocationBound
  rw [stackExecutionCost, releaseRun]
  simp only [Flapjack.StackSemControl.fixClock, Nat.min_self]
  rw [callCost]
  simpa [stackExecutionCost, refinedRemovalLocalPrice, removalLocalPrice,
    nativePriceWithGap, Flapjack.StackSemStateOps.decClock, Nat.add_assoc] using
    Nat.add_le_add_right localBound
      (stackExecutionCost (fun p _ => refinedRemovalLocalPrice 6 bounds p) body
        {Flapjack.StackSemStateOps.decClock source with
          stackSpace := source.stackSpace + released - allocated})

#print axioms optimizedTail_executionCost_le
end InitECandidate.Runtime.StackRawCall
