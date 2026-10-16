import Flapjack.Compiler.Backend.StackRemove.Proofs.StackAllocSimulation
set_option maxRecDepth 10000

namespace InitECandidate.Runtime.StackRemove
open Flapjack Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackLang
open Flapjack.Compiler.Backend.StackRemove.StackAllocSimulation

/-- The original arbitrary-count allocation simulation with the same witnesses,
but retaining their explicit extra-clock ceiling. -/
theorem evaluateSingleStackAlloc_bounded {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer count : Nat)
    (source target postSource : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : stateRelHOL jump bounds pointer source target ∧
      (result, postSource) = (if source.stackSpace < count then
        (some (.halt (.word 2)), StackSemStateOps.emptyEnv source)
        else (none, {source with stackSpace := source.stackSpace - count})) ∧
      count ≠ 0 ∧ count ≤ maxStackAlloc) :
    ∃ clock, clock ≤ 1 ∧ ∃ postTarget,
      StackSemEvaluate.evaluate (singleStackAlloc jump pointer count,
        {target with clock := target.clock + clock}) = (result, postTarget) ∧
      (if source.stackSpace < count then postTarget.ffi = postSource.ffi
       else stateRelHOL jump bounds pointer postSource postTarget) := by
  classical
  rcases hypothesis with ⟨relation, output, _nonzero, countBound⟩
  obtain ⟨base, baseLookup, lower, upper, pointerLookup, _heap⟩ :=
    StackPointer.stateRelGetVarK jump bounds pointer source target relation
  change target.regs.lookup (pointer + 1) = some (.word base) at baseLookup
  change target.regs.lookup pointer = some (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace)) at pointerLookup
  have good : goodDimindex width := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have spaceBound : source.stackSpace ≤ source.stack.length := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have comparison := AllocationArithmetic.allocationGuard base source.stackSpace source.stack.length count good lower upper spaceBound countBound
  have guard : Compiler.Encoders.Asm.wordCmpHOL .lower
      (base + bytesInWord width * BitVec.ofNat width source.stackSpace - wordOffset count) base =
      decide (source.stackSpace < count) := by
    simp only [Compiler.Encoders.Asm.wordCmpHOL, comparison]
  have codeLookup : sptLookup stackErrLab target.code = some (haltInst (BitVec.ofNat width 2)) := relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have baseNe : pointer + 1 ≠ pointer := by omega
  by_cases overflow : source.stackSpace < count
  · rw [if_pos overflow] at output
    rcases Prod.mk.inj output with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    simp only [overflow, decide_true] at guard
    cases jump with
    | false =>
      refine ⟨1, by decide, StackSemStateOps.emptyEnv {target with clock := target.clock + 1}, ?_, ?_⟩
      · simp [singleStackAlloc,  StackSemStateOps.emptyEnv, StackSemEvaluate.evaluate_seq, StackSemEvaluate.evaluate_inst,
          StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
          StackSemExpressions.assign, StackSemExpressions.wordExp, pointerLookup,
          wordOpHOL, wordOp, StackSemControl.fixClock,
          StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
          StackSemEvaluate.evaluate_ite,
          StackSemStateOps.getVar, StackSemStateOps.getVarImm, Compiler.Encoders.Asm.HolRegImm.toWordRegImm,
          wordSemWordCmp, baseLookup, guard,
            haltInst,
          StackSemEvaluate.evaluate_halt]
      · simpa [overflow, StackSemStateOps.emptyEnv] using relation.2.2.2.2.2.2.2.2.2.1
    | true =>
      refine ⟨1, by decide, StackSemStateOps.emptyEnv target, ?_, ?_⟩
      · simp [singleStackAlloc,  StackSemStateOps.emptyEnv, StackSemEvaluate.evaluate_seq, StackSemEvaluate.evaluate_inst,
          StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
          StackSemExpressions.assign, StackSemExpressions.wordExp, pointerLookup,
          wordOpHOL, wordOp, StackSemControl.fixClock,
          StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
           StackSemEvaluate.evaluate_jumpLower,
          StackSemStateOps.getVar,
           baseLookup, guard,
          StackSemControl.findCode, codeLookup, haltInst,
          StackSemEvaluate.evaluate_halt, StackSemStateOps.decClock, StackSemControl.badFunReturn]
      · simpa [overflow, StackSemStateOps.emptyEnv] using relation.2.2.2.2.2.2.2.2.2.1
  · rw [if_neg overflow] at output
    rcases Prod.mk.inj output with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    refine ⟨0, by decide, StackSemStateOps.setVar pointer
      (.word (base + bytesInWord width * BitVec.ofNat width source.stackSpace - wordOffset count)) target, ?_, ?_⟩
    · cases jump <;> simp [singleStackAlloc,  StackSemEvaluate.evaluate_seq,
        StackSemEvaluate.evaluate_inst, StackSemInst.instHOL, StackSemIntegerInstructions.instInteger,
        StackSemExpressions.assign, StackSemExpressions.wordExp, pointerLookup, wordOpHOL, wordOp,
        StackSemControl.fixClock, StackSemStateOps.setVar, HolFiniteMapExact.lookup_updateEq, FUPDATE_HOL,
        StackSemEvaluate.evaluate_ite, StackSemEvaluate.evaluate_jumpLower, StackSemEvaluate.evaluate_skip,
        StackSemStateOps.getVar, StackSemStateOps.getVarImm, Compiler.Encoders.Asm.HolRegImm.toWordRegImm, wordSemWordCmp, baseLookup, guard, overflow]
    · rw [if_neg overflow]
      simpa only [pointerLookup] using stateRelAllocStep jump bounds pointer count source target relation (Nat.le_of_not_gt overflow)
theorem runAlloc_bounded {width : Nat} [NeZero width] {C F : Type}
    (count : Nat) (jump : Bool) (bounds : BitVec width × BitVec width) (pointer : Nat)
    (source target : StackSemStateFiniteExact width C F)
    (relation : stateRelHOL jump bounds pointer source target) :
    ∃ clock, clock ≤ 1 ∧ ∃ postTarget,
      StackSemEvaluate.evaluate (stackAlloc jump pointer count, {target with clock := clock + target.clock}) =
        ((if source.stackSpace < count then some (.halt (.word 2)) else none), postTarget) ∧
      (if source.stackSpace < count then postTarget.ffi = source.ffi
       else stateRelHOL jump bounds pointer {source with stackSpace := source.stackSpace - count} postTarget) := by
  classical
  induction count using Nat.strongRecOn generalizing source target with
  | ind count ih =>
    by_cases zero : count = 0
    · subst count
      exact ⟨0, by decide, target, by simp [stackAlloc, StackSemEvaluate.evaluate_skip], by simpa using relation⟩
    by_cases small : count ≤ maxStackAlloc
    · let expectedSource := if source.stackSpace < count then StackSemStateOps.emptyEnv source
        else {source with stackSpace := source.stackSpace - count}
      obtain ⟨clock, bound, postTarget, run, post⟩ := evaluateSingleStackAlloc_bounded jump bounds pointer count
        source target expectedSource (if source.stackSpace < count then some (.halt (.word 2)) else none)
        ⟨relation, by dsimp [expectedSource]; split <;> rfl, zero, small⟩
      refine ⟨clock, bound, postTarget, ?_, ?_⟩
      · rw [stackAlloc, if_neg zero, if_pos small]
        simpa only [Nat.add_comm] using run
      · by_cases overflow : source.stackSpace < count
        · simpa [overflow, expectedSource, StackSemStateOps.emptyEnv] using post
        · simpa [overflow, expectedSource] using post
    by_cases firstOverflow : source.stackSpace < maxStackAlloc
    · have overflow : source.stackSpace < count := by omega
      obtain ⟨clock, bound, postTarget, run, post⟩ := evaluateSingleStackAlloc_bounded jump bounds pointer maxStackAlloc
        source target (StackSemStateOps.emptyEnv source) (some (.halt (.word 2)))
        ⟨relation, by rw [if_pos firstOverflow], by decide, Nat.le_refl _⟩
      have firstRun : StackSemEvaluate.evaluate (singleStackAlloc jump pointer maxStackAlloc,
          {target with clock := clock + target.clock}) = (some (.halt (.word 2)),postTarget) := by
        simpa only [Nat.add_comm] using run
      refine ⟨clock, bound, (StackSemControl.fixClock {target with clock := clock + target.clock}
        ((some (.halt (.word 2)) : Option (StackSemResult width)), postTarget)).2, ?_, ?_⟩
      · rw [stackAlloc, if_neg zero, if_neg small, StackSemEvaluate.evaluate_seq, firstRun]
        simp [StackSemControl.fixClock, overflow]
      · simpa [overflow, firstOverflow, StackSemControl.fixClock, StackSemStateOps.emptyEnv] using post
    · have available : maxStackAlloc ≤ source.stackSpace := Nat.le_of_not_gt firstOverflow
      let nextSource := {source with stackSpace := source.stackSpace - maxStackAlloc}
      let nextTarget := StackSemStateOps.setVar pointer
        (.word ((match target.regs.lookup pointer with | some (.word word) => word | _ => 0) - wordOffset maxStackAlloc)) target
      have nextRelation : stateRelHOL jump bounds pointer nextSource nextTarget :=
        stateRelAllocStep jump bounds pointer maxStackAlloc source target relation available
      obtain ⟨clock, bound, postTarget, run, post⟩ := ih (count - maxStackAlloc)
        (by simp only [maxStackAlloc] at *; omega) nextSource nextTarget nextRelation
      have overflowEq : nextSource.stackSpace < count - maxStackAlloc ↔ source.stackSpace < count := by
        dsimp [nextSource]; omega
      have subtractionEq : (source.stackSpace - maxStackAlloc) - (count - maxStackAlloc) = source.stackSpace - count := by omega
      refine ⟨clock, bound, postTarget, ?_, ?_⟩
      · rw [stackAlloc, if_neg zero, if_neg small, StackSemEvaluate.evaluate_seq]
        have firstRun := runSingleAvailable jump bounds pointer maxStackAlloc (clock + target.clock)
          source target relation available (Nat.le_refl _)
        have presented : StackSemEvaluate.evaluate (singleStackAlloc jump pointer maxStackAlloc,
          {target with clock := clock + target.clock}) = (none, {nextTarget with clock := clock + nextTarget.clock}) := by
          rw [firstRun]
          dsimp only [nextTarget, StackSemStateOps.setVar]
          cases read : target.regs.lookup pointer with
          | none => rfl
          | some value => cases value <;> rfl
        rw [presented]
        have clamp : StackSemControl.fixClock {target with clock := clock + target.clock}
            ((none : Option (StackSemResult width)), {nextTarget with clock := clock + nextTarget.clock}) =
            (none, {nextTarget with clock := clock + nextTarget.clock}) := by
          simp [StackSemControl.fixClock, nextTarget, StackSemStateOps.setVar]
        rw [clamp]
        simpa only [overflowEq] using run
      · simpa only [overflowEq, nextSource, subtractionEq] using post
attribute [local instance] Classical.propDecidable
/-- Full original arbitrary-count stack allocation simulation, including both
native overflow modes and the original universally quantified non-Halt branch. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem evaluateStackAlloc_bounded {width : Nat} [NeZero width] {C F : Type}
    (jump : Bool) (bounds : BitVec width × BitVec width) (pointer count : Nat)
    (source target postSource : StackSemStateFiniteExact width C F)
    (result : Option (StackSemResult width))
    (hypothesis : StackSemEvaluate.evaluate ((.stackAlloc count), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target) :
    ∃ clock, clock ≤ 1 ∧ ∃ postTarget,
      StackSemEvaluate.evaluate (stackAlloc jump pointer count,
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (if ∀ word, result ≠ some (.halt word) then
        stateRelHOL jump bounds pointer postSource postTarget else postTarget.ffi = postSource.ffi) := by
  classical
  rcases hypothesis with ⟨sourceRun, _notError, relation⟩
  rw [StackSemEvaluate.evaluate_stackAlloc] at sourceRun
  simp only [relation.1, Bool.not_true, Bool.false_eq_true, if_false] at sourceRun
  obtain ⟨clock, bound, postTarget, targetRun, post⟩ := runAlloc_bounded count jump bounds pointer source target relation
  by_cases overflow : source.stackSpace < count
  · rw [if_pos overflow] at sourceRun targetRun post
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    refine ⟨clock, bound, postTarget, targetRun, ?_⟩
    simpa [StackSemStateOps.emptyEnv] using post
  · rw [if_neg overflow] at sourceRun targetRun post
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    exact ⟨clock, bound, postTarget, targetRun, by simpa [relation.1] using post⟩
theorem compCorrectStackAlloc_bounded {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (count : Nat)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate ((.stackAlloc count), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound ((.stackAlloc count) : HolProg width) pointer) :
    ∃ (clock : Nat), clock ≤ 1 ∧ ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.stackAlloc count),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  classical
  rcases hypothesis with ⟨sourceRun, notError, relation, _bound⟩
  obtain ⟨clock, bound, postTarget, targetRun, postRelation⟩ :=
    evaluateStackAlloc_bounded jump bounds pointer count source target postSource result
      ⟨sourceRun, notError, relation⟩
  refine ⟨clock, bound, postTarget, ?_, ?_⟩
  · simpa only [comp] using targetRun
  · cases result with
    | none => simpa using postRelation
    | some result =>
      cases result <;> simp at postRelation <;>
        first | exact postRelation | exact postRelation.2.2.2.2.2.2.2.2.2.1
#print axioms compCorrectStackAlloc_bounded
#print axioms evaluateStackAlloc_bounded
end InitECandidate.Runtime.StackRemove
