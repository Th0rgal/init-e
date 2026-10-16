import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Atoms
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Control
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Instructions
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.Locations
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.CodeBufferWrite
import Flapjack.Compiler.Backend.StackRemove.Proofs.CompCorrect.HeapOperation

namespace InitECandidate.Runtime.StackRemove.Zero
open Flapjack Flapjack.Compiler.Backend.StackRemove Flapjack.Compiler.Backend.StackLang
open Flapjack.StackSemEvaluate Flapjack.StackSemStateOps Flapjack.Compiler.Encoders.Asm
open Flapjack.Compiler.Backend.StackRemove.CompCorrect.CodeBufferWrite
open Flapjack.Compiler.Backend.StackRemove.CompCorrect
theorem compCorrectSkip {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate (.skip, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound (.skip : HolProg width) pointer) :
    ∃ (clock : Nat), clock = 0 ∧ ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer .skip,
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, _notError, relation, _bound⟩
  rw [StackSemEvaluate.evaluate_skip] at sourceRun
  rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
  subst result
  subst postSource
  refine ⟨0, rfl, target, ?_, relation⟩
  simp [comp, StackSemEvaluate.evaluate_skip]

/-- Full original Halt case with its unchanged existential result. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectHalt {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (register : Nat)
    (hypothesis : StackSemEvaluate.evaluate ((.halt register), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound ((.halt register) : HolProg width) pointer) :
    ∃ (clock : Nat), clock = 0 ∧ ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.halt register),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have registerBound : register < pointer := bound
  have lookupEq := RelationLaws.stateRelGetVar jump bounds pointer register source target
    ⟨relation, registerBound⟩
  rw [StackSemEvaluate.evaluate_halt] at sourceRun
  cases sourceLookup : StackSemStateOps.getVar register source with
  | none =>
    rw [sourceLookup] at sourceRun
    have resultEq := (Prod.mk.inj sourceRun).1
    exact (notError resultEq.symm).elim
  | some value =>
    rw [sourceLookup] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    have targetLookup : StackSemStateOps.getVar register target = some value :=
      lookupEq.symm.trans sourceLookup
    refine ⟨0, rfl, StackSemStateOps.emptyEnv target, ?_, ?_⟩
    · simpa only [comp, Nat.zero_add] using
        (StackSemEvaluate.evaluate_halt register target).trans
          (by rw [targetLookup])
    · exact (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1

/-- Full original Alloc case with its unchanged existential result. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectAlloc {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (register : Nat)
    (hypothesis : StackSemEvaluate.evaluate ((.alloc register), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound ((.alloc register) : HolProg width) pointer) :
    ∃ (clock : Nat), clock = 0 ∧ ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.alloc register),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, _bound⟩
  have noAlloc := relation
  simp only [stateRelHOL] at noAlloc
  have flag := noAlloc.2.2.2.2.2.1
  rw [StackSemEvaluate.evaluate_alloc] at sourceRun
  simp only [flag, Bool.not_false, ite_true] at sourceRun
  have resultEq := (Prod.mk.inj sourceRun).1
  exact (notError resultEq.symm).elim

theorem compCorrectTick {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate (.tick, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound (.tick : HolProg width) pointer) :
    ∃ (clock : Nat), clock = 0 ∧ ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer .tick,
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, _notError, relation, _bound⟩
  have clocks : target.clock = source.clock := relation.2.2.2.2.2.2.2.2.1
  rw [StackSemEvaluate.evaluate_tick] at sourceRun
  by_cases zero : source.clock = 0
  · simp only [zero, ite_true] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    refine ⟨0, rfl, StackSemStateOps.emptyEnv target, ?_, ?_⟩
    · simpa only [comp, Nat.zero_add] using
        (StackSemEvaluate.evaluate_tick target).trans (by simp [clocks, zero])
    · exact (RelationLaws.stateRelConst jump bounds pointer source target relation).2.2.2.2.1
  · simp only [zero, ite_false] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    refine ⟨0, rfl, StackSemStateOps.decClock target, ?_, ?_⟩
    · simpa only [comp, Nat.zero_add] using
        (StackSemEvaluate.evaluate_tick target).trans (by simp [clocks, zero])
    · exact RelationLaws.stateRelDecClock jump bounds pointer source target relation

/-- Full original Return case, with no added successful-run or clock premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectReturn {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (register : Nat)
    (hypothesis : StackSemEvaluate.evaluate ((.ret register), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound ((.ret register) : HolProg width) pointer) :
    ∃ (clock : Nat), clock = 0 ∧ ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.ret register),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have registerBound : register < pointer := bound
  have lookupEq := RelationLaws.stateRelGetVar jump bounds pointer register source target
    ⟨relation, registerBound⟩
  rw [StackSemEvaluate.evaluate_ret] at sourceRun
  cases sourceLookup : StackSemStateOps.getVar register source with
  | none =>
    rw [sourceLookup] at sourceRun
    have resultEq := (Prod.mk.inj sourceRun).1
    exact (notError resultEq.symm).elim
  | some value =>
    cases value with
    | word value =>
      rw [sourceLookup] at sourceRun
      have resultEq := (Prod.mk.inj sourceRun).1
      exact (notError resultEq.symm).elim
    | loc block offset =>
      rw [sourceLookup] at sourceRun
      rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
      subst result
      subst postSource
      have targetLookup : StackSemStateOps.getVar register target = some (.loc block offset) :=
        lookupEq.symm.trans sourceLookup
      refine ⟨0, rfl, target, ?_, relation⟩
      simpa only [comp, Nat.zero_add] using
        (StackSemEvaluate.evaluate_ret register target).trans (by rw [targetLookup])

/-- Full original Raise case, with no added successful-run or clock premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectRaise {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (register : Nat)
    (hypothesis : StackSemEvaluate.evaluate ((.raise register), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound ((.raise register) : HolProg width) pointer) :
    ∃ (clock : Nat), clock = 0 ∧ ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.raise register),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have registerBound : register < pointer := bound
  have lookupEq := RelationLaws.stateRelGetVar jump bounds pointer register source target
    ⟨relation, registerBound⟩
  rw [StackSemEvaluate.evaluate_raise] at sourceRun
  cases sourceLookup : StackSemStateOps.getVar register source with
  | none =>
    rw [sourceLookup] at sourceRun
    have resultEq := (Prod.mk.inj sourceRun).1
    exact (notError resultEq.symm).elim
  | some value =>
    cases value with
    | word value =>
      rw [sourceLookup] at sourceRun
      have resultEq := (Prod.mk.inj sourceRun).1
      exact (notError resultEq.symm).elim
    | loc block offset =>
      rw [sourceLookup] at sourceRun
      rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
      subst result
      subst postSource
      have targetLookup : StackSemStateOps.getVar register target = some (.loc block offset) :=
        lookupEq.symm.trans sourceLookup
      refine ⟨0, rfl, target, ?_, relation⟩
      simpa only [comp, Nat.zero_add] using
        (StackSemEvaluate.evaluate_raise register target).trans (by rw [targetLookup])

/-- Full original Break case, with no added successful-run or clock premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectBreak {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (label : Nat)
    (hypothesis : StackSemEvaluate.evaluate ((.break label), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound ((.break label) : HolProg width) pointer) :
    ∃ (clock : Nat), clock = 0 ∧ ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.break label),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, _notError, relation, _bound⟩
  rw [StackSemEvaluate.evaluate_break] at sourceRun
  rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
  subst result
  subst postSource
  refine ⟨0, rfl, target, ?_, relation⟩
  simp [comp, StackSemEvaluate.evaluate_break]

/-- Full original Continue case, with no added successful-run or clock premise. -/
-- riscv-mi: depends on reduced integer-only carriers; not an exact full-HOL port.
theorem compCorrectContinue {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (label : Nat)
    (hypothesis : StackSemEvaluate.evaluate ((.continue label), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound ((.continue label) : HolProg width) pointer) :
    ∃ (clock : Nat), clock = 0 ∧ ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.continue label),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, _notError, relation, _bound⟩
  rw [StackSemEvaluate.evaluate_continue] at sourceRun
  rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
  subst result
  subst postSource
  refine ⟨0, rfl, target, ?_, relation⟩
  simp [comp, StackSemEvaluate.evaluate_continue]

theorem compCorrectInst {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (instruction : HolInst width)
    (hypothesis : StackSemEvaluate.evaluate (.inst instruction, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound (.inst instruction) pointer) :
    ∃ (clock : Nat), clock = 0 ∧ ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.inst instruction),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  rw [StackSemEvaluate.evaluate_inst] at sourceRun
  cases instRun : StackSemInst.instHOL instruction source with
  | none =>
    rw [instRun] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  | some state =>
    rw [instRun] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    have instructionBound : Flapjack.Compiler.Backend.StackProps.regBoundInst instruction pointer := bound
    obtain ⟨postTarget, targetRun, postRelation⟩ :=
      InstructionSimulation.stateRelInst jump bounds pointer instruction source target state
        ⟨relation, instructionBound, instRun⟩
    refine ⟨0, rfl, postTarget, ?_, postRelation⟩
    simpa only [comp, Nat.zero_add] using
      (StackSemEvaluate.evaluate_inst instruction target).trans (by rw [targetRun])

theorem compCorrectLocValue {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (register first second : Nat)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : StackSemEvaluate.evaluate ((.locValue register first second), source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound ((.locValue register first second) : HolProg width) pointer) :
    ∃ (clock : Nat), clock = 0 ∧ ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.locValue register first second),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  classical
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  rw [StackSemEvaluate.evaluate_locValue] at sourceRun
  by_cases checked : StackSem.locCheckExact source.code (first, second)
  · rw [if_pos checked] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    have codeRelation : codeRelHOL jump bounds pointer source.code target.code :=
      relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    have targetChecked := LabelPreservation.codeRelLocCheck jump bounds pointer
      source.code target.code first second ⟨codeRelation, checked⟩
    have registerBound : register < pointer := bound
    refine ⟨0, rfl, StackSemStateOps.setVar register (.loc first second) target, ?_, ?_⟩
    · simp [comp, StackSemEvaluate.evaluate_locValue, targetChecked]
    · exact StateUpdates.stateRelSetVar jump bounds pointer register (.loc first second)
        source target ⟨relation, registerBound⟩
  · rw [if_neg checked] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
theorem compCorrectCodeBufferWrite {width : Nat} [NeZero width] {C F : Type}
    (first second : Nat)
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (hypothesis : evaluate (.codeBufferWrite first second, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound (.codeBufferWrite first second : HolProg width) pointer) :
    ∃ clock, clock = 0 ∧ ∃ postTarget,
      evaluate (comp jump bounds pointer (.codeBufferWrite first second),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  change first < pointer ∧ second < pointer at bound
  have readFirst := RelationLaws.stateRelGetVar jump bounds pointer first source target ⟨relation, bound.1⟩
  have readSecond := RelationLaws.stateRelGetVar jump bounds pointer second source target ⟨relation, bound.2⟩
  change source.regs.lookup first = target.regs.lookup first at readFirst
  change source.regs.lookup second = target.regs.lookup second at readSecond
  have buffers : target.codeBuffer = source.codeBuffer := relation.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [evaluate_codeBufferWrite] at sourceRun
  cases hFirst : getVar first source with
  | none =>
    simp only [hFirst] at sourceRun
    exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
  | some left =>
    cases left with
    | loc name offset =>
      simp only [hFirst] at sourceRun
      exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
    | word left =>
      cases hSecond : getVar second source with
      | none =>
        simp only [hFirst, hSecond] at sourceRun
        exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
      | some right =>
        cases right with
        | loc name offset =>
          simp only [hFirst, hSecond] at sourceRun
          exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
        | word right =>
          simp only [hFirst, hSecond] at sourceRun
          cases write : wordSemBufferWrite source.codeBuffer left (right.setWidth 8) with
          | none =>
            simp only [write] at sourceRun
            exact False.elim (notError (Prod.mk.inj sourceRun).1.symm)
          | some buffer =>
            simp only [write] at sourceRun
            rcases Prod.mk.inj sourceRun with ⟨resultEq, postEq⟩
            subst result
            subst postSource
            have targetFirst : target.regs.lookup first = some (.word left) := readFirst.symm.trans hFirst
            have targetSecond : target.regs.lookup second = some (.word right) := readSecond.symm.trans hSecond
            refine ⟨0, rfl, {target with codeBuffer := buffer}, ?_, ?_⟩
            · simpa only [comp, Nat.zero_add] using
                (evaluate_codeBufferWrite first second target).trans (by
                  simp only [getVar, targetFirst, targetSecond, buffers, write])
            · exact stateRelCodeBuffer jump bounds pointer source target buffer relation
theorem compCorrectOpCurrHeap {width : Nat} [NeZero width] {C F : Type}
    (source : StackSemStateFiniteExact width C F) (result : Option (StackSemResult width))
    (postSource target : StackSemStateFiniteExact width C F)
    (pointer : Nat) (bounds : BitVec width × BitVec width) (jump : Bool)
    (operator : BinOp) (destination input : Nat)
    (hypothesis : StackSemEvaluate.evaluate (.opCurrHeap operator destination input, source) = (result, postSource) ∧
      result ≠ some .error ∧ stateRelHOL jump bounds pointer source target ∧
      Flapjack.Compiler.Backend.StackProps.regBound (.opCurrHeap operator destination input : HolProg width) pointer) :
    ∃ (clock : Nat), clock = 0 ∧ ∃ (postTarget : StackSemStateFiniteExact width C F),
      StackSemEvaluate.evaluate (comp jump bounds pointer (.opCurrHeap operator destination input),
        {target with clock := clock + target.clock}) = (result, postTarget) ∧
      (match result with
       | some (.halt _) | some .timeOut | some (.finalFFI _) => postTarget.ffi = postSource.ffi
       | _ => stateRelHOL jump bounds pointer postSource postTarget) := by
  rcases hypothesis with ⟨sourceRun, notError, relation, bound⟩
  have useStore : source.useStore = true := relation.2.1
  have regEq : target.regs.lookup input = source.regs.lookup input :=
    relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 input bound.2
  have heapEq : target.regs.lookup (pointer + 2) = source.store.lookup .currHeap :=
    relation.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have expressionEq : StackSemExpressions.wordExp target (.op operator [.var input, .var (pointer + 2)]) =
      StackSemExpressions.wordExp source (.op operator [.var input, .lookup .currHeap]) := by
    simp [StackSemExpressions.wordExp, regEq, heapEq]
  rw [StackSemEvaluate.evaluate_opCurrHeap] at sourceRun
  simp only [useStore, not_true_eq_false, ite_false] at sourceRun
  cases valueRun : StackSemExpressions.wordExp source (.op operator [.var input, .lookup .currHeap]) with
  | none =>
    rw [valueRun] at sourceRun
    exact (notError (Prod.mk.inj sourceRun).1.symm).elim
  | some value =>
    rw [valueRun] at sourceRun
    rcases Prod.mk.inj sourceRun with ⟨resultEq, stateEq⟩
    subst result
    subst postSource
    refine ⟨0, rfl, StackSemStateOps.setVar destination (.word value) target, ?_, ?_⟩
    · have different : pointer + 2 ≠ input := by have := bound.2; omega
      simp only [comp, Nat.zero_add, StackSemEvaluate.evaluate_inst,
        StackSemInst.instHOL, StackSemIntegerInstructions.instInteger, Option.join_some]
      simp [different, StackSemExpressions.assign, expressionEq, valueRun]
    · exact StateUpdates.stateRelSetVar jump bounds pointer destination (.word value) source target
        ⟨relation, bound.1⟩

#print axioms compCorrectSkip
#print axioms compCorrectHalt
#print axioms compCorrectAlloc
#print axioms compCorrectTick
#print axioms compCorrectReturn
#print axioms compCorrectRaise
#print axioms compCorrectBreak
#print axioms compCorrectContinue
#print axioms compCorrectInst
#print axioms compCorrectLocValue
#print axioms compCorrectCodeBufferWrite
#print axioms compCorrectOpCurrHeap
end InitECandidate.Runtime.StackRemove.Zero
