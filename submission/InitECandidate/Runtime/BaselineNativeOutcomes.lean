import InitECandidate.Runtime.BaselineFrontendNative
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target

theorem baseline_word_ffi_native_uniform {input : Guest.InputBlob}
    (entry : BaselineRuntimeEntry input) (fuel : Nat)
    (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory)
    (event : HolFinalEvent)
    (run : WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {entryWordState entry.cfg entry.source with clock := fuel} = (some (.finalFfi event), wordPost)) :
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeFuel fuel ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt outcome, native, final.ffi) ∧
      ((outcome = .ffiOutcome event ∧ final.ffi = wordPost.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents wordPost.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨wc,rc,mc,lc,final,outcome,count,native,wb,rb,mb,lb,nb,evaluated,observation⟩ :=
    baseline_word_ffi_native_affine entry fuel wordPost event run
  have actualRemoval := baseline_removeWork_ceiling entry rc
  have word := baseline_wordWork_ceiling entry fuel
  have wordCap : wc ≤ baselineWordFuel fuel := by unfold baselineWordFuel; omega
  have rawCap : rc ≤ baselineRawFuel fuel := by unfold baselineRawFuel; omega
  have removal := Nat.mul_le_mul_left baselineBitmapScale (workCeiling_fuel_mono baselineRemovalLimit
    (sizeOf (.call none (.inl BvlToBvi.initGlobalsLocation) none : StackLang.HolProg 64)) rc (baselineRawFuel fuel) rawCap)
  have removedCap : mc ≤ baselineRemovedFuel fuel := by unfold baselineRemovedFuel; omega
  have scaled := Nat.mul_le_mul_left (2 * baselineNamedLimit + 3) removedCap
  have labels : mc - 1 + lc ≤ (2 * baselineNamedLimit + 3) * baselineRemovedFuel fuel + 4 * baselineNamedLimit := by
    have localBound : mc - 1 + lc ≤ (2 * baselineNamedLimit + 3) * mc + 4 * baselineNamedLimit := by
      rw [show 2 * baselineNamedLimit + 3 = (2 * baselineNamedLimit + 2) + 1 by omega, Nat.add_mul, Nat.one_mul]
      omega
    exact Nat.le_trans localBound (Nat.add_le_add_right scaled _)
  have nativeCap := Nat.mul_le_mul_left 14467153 labels
  exact ⟨final,outcome,count,native,Nat.le_trans nb nativeCap,evaluated,observation⟩

theorem baseline_word_resource_native_uniform {input : Guest.InputBlob}
    (entry : BaselineRuntimeEntry input) (fuel : Nat)
    (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory)
    (run : WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {entryWordState entry.cfg entry.source with clock := fuel} = (some .notEnoughSpace, wordPost)) :
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ count native,
      count ≤ baselineNativeFuel fuel ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt .resourceLimitHit, native, final.ffi) ∧
      (final.ffi = wordPost.ffi ∨
        (List.IsPrefix final.ffi.ioEvents wordPost.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨wc,rc,mc,lc,final,count,native,wb,rb,mb,lb,nb,evaluated,observation⟩ :=
    baseline_word_resource_native_affine entry fuel wordPost run
  have actualRemoval := baseline_removeWork_ceiling entry rc
  have word := baseline_wordWork_ceiling entry fuel
  have wordCap : wc ≤ baselineWordFuel fuel := by unfold baselineWordFuel; omega
  have rawCap : rc ≤ baselineRawFuel fuel := by unfold baselineRawFuel; omega
  have removal := Nat.mul_le_mul_left baselineBitmapScale (workCeiling_fuel_mono baselineRemovalLimit
    (sizeOf (.call none (.inl BvlToBvi.initGlobalsLocation) none : StackLang.HolProg 64)) rc (baselineRawFuel fuel) rawCap)
  have removedCap : mc ≤ baselineRemovedFuel fuel := by unfold baselineRemovedFuel; omega
  have scaled := Nat.mul_le_mul_left (2 * baselineNamedLimit + 3) removedCap
  have labels : mc - 1 + lc ≤ (2 * baselineNamedLimit + 3) * baselineRemovedFuel fuel + 4 * baselineNamedLimit := by
    have localBound : mc - 1 + lc ≤ (2 * baselineNamedLimit + 3) * mc + 4 * baselineNamedLimit := by
      rw [show 2 * baselineNamedLimit + 3 = (2 * baselineNamedLimit + 2) + 1 by omega, Nat.add_mul, Nat.one_mul]
      omega
    exact Nat.le_trans localBound (Nat.add_le_add_right scaled _)
  have nativeCap := Nat.mul_le_mul_left 14467153 labels
  exact ⟨final,count,native,Nat.le_trans nb nativeCap,evaluated,observation⟩

theorem baseline_frontend_ffi_native {input : Guest.InputBlob}
    (entry : BaselineRuntimeEntry input) (fuel : Nat)
    (post : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory)
    (event : HolFinalEvent)
    (run : WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {entryFrontendState entry with clock := fuel} = (some (.finalFfi event),post)) :
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeFuel fuel ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .ffiOutcome event ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          post.stackMax.getD (post.stackLimit + 1) > post.stackLimit)) := by
  obtain ⟨optimized, evaluated, ffi, _, stack, limit⟩ :=
    baseline_frontend_optimized_run entry fuel _ post run (by simp)
  obtain ⟨final,outcome,count,native,bound,nativeRun,observation⟩ :=
    baseline_word_ffi_native_uniform entry fuel optimized event evaluated
  rw [ffi,stack,limit] at observation
  exact ⟨final,outcome,count,native,bound,nativeRun,observation⟩

theorem baseline_frontend_resource_native {input : Guest.InputBlob}
    (entry : BaselineRuntimeEntry input) (fuel : Nat)
    (post : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory)
    (run : WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {entryFrontendState entry with clock := fuel} = (some .notEnoughSpace,post)) :
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ count native,
      count ≤ baselineNativeFuel fuel ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt .resourceLimitHit,native,final.ffi) ∧
      (final.ffi = post.ffi ∨
        (List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          post.stackMax.getD (post.stackLimit + 1) > post.stackLimit)) := by
  obtain ⟨optimized, evaluated, ffi, _, stack, limit⟩ :=
    baseline_frontend_optimized_run entry fuel _ post run (by simp)
  obtain ⟨final,count,native,bound,nativeRun,observation⟩ :=
    baseline_word_resource_native_uniform entry fuel optimized evaluated
  rw [ffi,stack,limit] at observation
  exact ⟨final,count,native,bound,nativeRun,observation⟩

/-- Increasing a frontend fuel ceiling also increases the full native ceiling. -/
theorem baselineNativeFuel_mono (a b : Nat) (less : a ≤ b) :
    baselineNativeFuel a ≤ baselineNativeFuel b := by
  have word := workCeiling_fuel_mono baselineWordLimit
    (sizeOf (.call none (some BvlToBvi.initGlobalsLocation) [0] none : WordLangProgHOL (BitVec 64))) a b less
  have wordCap : baselineWordFuel a ≤ baselineWordFuel b := Nat.add_le_add less word
  have raw : baselineRawFuel a ≤ baselineRawFuel b := Nat.mul_le_mul_left 2 wordCap
  have removal := Nat.mul_le_mul_left baselineBitmapScale (workCeiling_fuel_mono baselineRemovalLimit
    (sizeOf (.call none (.inl BvlToBvi.initGlobalsLocation) none : StackLang.HolProg 64))
    (baselineRawFuel a) (baselineRawFuel b) raw)
  have removed : baselineRemovedFuel a ≤ baselineRemovedFuel b :=
    Nat.add_le_add_right (Nat.add_le_add raw removal) 1
  exact Nat.mul_le_mul_left 14467153
    (Nat.add_le_add_right (Nat.mul_le_mul_left (2 * baselineNamedLimit + 3) removed) _)

#print axioms baselineNativeFuel_mono
#print axioms baseline_word_ffi_native_uniform
#print axioms baseline_word_resource_native_uniform
#print axioms baseline_frontend_ffi_native
#print axioms baseline_frontend_resource_native
end InitECandidate.Runtime
