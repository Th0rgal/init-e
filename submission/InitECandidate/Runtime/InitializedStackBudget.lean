import InitECandidate.Runtime.HaltStubBudget
import Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

namespace InitECandidate.Runtime.StackToLab
open Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Backend.StackLang Flapjack.Compiler.Backend.LabSem
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

/-- Initialization discharges the compiler state relation and entry location.
The source evaluation is at the actual named/removed initialized stage, not
assumed to be the original Pancake evaluation. -/
theorem initialized_halt_bounded {width : Nat} [NeZero width] {C F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (target : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (post : StackSemStateFiniteExact width C F) (value : BitVec width)
    (initialized : Assumptions stackConf dataConf maxHeap sp offset bitmaps code target saveRegs dataSp oracle)
    (run : StackSemEvaluate.evaluate ((.call none (.inl 0) none : HolProg width),
      s3 stackConf dataConf maxHeap sp offset code target saveRegs oracle) =
        (some (.halt (.word value)), post)) :
    ∃ clocks final, clocks ≤ entryWork 0 (s3 stackConf dataConf maxHeap sp offset code target saveRegs oracle) ∧
      evaluate { target with clock := target.clock - 1 + clocks } =
        (if value = 0 then .halt .success else .halt .resourceLimitHit, final) ∧ final.ffi = post.ffi := by
  obtain ⟨clocks, bound, result, final, evaluated, _, halted, _, ffi, _, _⟩ :=
    flattenEntry_bounded ⟨run, stateRel_s3 initialized, locToPc_start initialized,
      by simp, fun _ => Or.inl ⟨value, rfl⟩⟩
  refine ⟨clocks, final, bound, ?_, ffi⟩
  rw [halted (.word value) rfl] at evaluated
  exact evaluated

/-- Initialization discharges the compiler state relation and entry location.
The source evaluation is at the actual named/removed initialized stage, not
assumed to be the original Pancake evaluation. -/
theorem initialized_ffi_bounded {width : Nat} [NeZero width] {C F : Type}
    (stackConf : StackToLab.Config) (dataConf : DataToWord.Config) (maxHeap sp : Nat)
    (offset : BitVec width × BitVec width) (bitmaps : List (BitVec width))
    (code : List (Nat × HolProg width)) (target : LabSem.State width C F)
    (saveRegs : Nat → Bool) (dataSp : Nat)
    (oracle : Nat → C × List (Nat × HolProg width) × List (BitVec width))
    (post : StackSemStateFiniteExact width C F) (event : HolFinalEvent)
    (initialized : Assumptions stackConf dataConf maxHeap sp offset bitmaps code target saveRegs dataSp oracle)
    (run : StackSemEvaluate.evaluate ((.call none (.inl 0) none : HolProg width),
      s3 stackConf dataConf maxHeap sp offset code target saveRegs oracle) =
        (some (.finalFFI event), post)) :
    ∃ clocks final, clocks ≤ entryWork 0 (s3 stackConf dataConf maxHeap sp offset code target saveRegs oracle) ∧
      evaluate { target with clock := target.clock - 1 + clocks } =
        (.halt (.ffiOutcome event), final) ∧ final.ffi = post.ffi := by
  obtain ⟨clocks, bound, result, final, evaluated, terminal, _, _, ffi, _, _⟩ :=
    flattenEntry_bounded ⟨run, stateRel_s3 initialized, locToPc_start initialized,
      by simp, fun _ => Or.inr (Or.inl ⟨event, rfl⟩)⟩
  refine ⟨clocks, final, bound, ?_, ffi⟩
  rw [terminal event rfl] at evaluated
  exact evaluated

#print axioms initialized_halt_bounded
#print axioms initialized_ffi_bounded
end InitECandidate.Runtime.StackToLab
