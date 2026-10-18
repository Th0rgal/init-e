import InitECandidate.Runtime.BaselineRemovalCeiling
import InitECandidate.Runtime.BaselineWordNativePathAffine
import InitECandidate.Runtime.BaselineNativeFuel
import InitECandidate.Runtime.StackRemoveAffineWork
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

/-- Actual baseline stack-removal overhead is affine in its entry fuel. -/
theorem baseline_removeAffineWork_bound {input : Guest.InputBlob}
    (entry : BaselineRuntimeEntry input) (fuel : Nat) :
    StackRemove.removeAffineWork (.call none (.inl BvlToBvi.initGlobalsLocation) none)
      {entry.source with clock := fuel} ≤
      baselineBitmapScale * ((2 * baselineRemovalLimit + 2) * fuel + 2 * baselineRemovalLimit) :=
  StackRemove.removeAffineWork_le baselineRemovalLimit baselineBitmapScale _ _
    (Nat.le_max_left _ _) (baseline_source_code_bounded entry fuel)
    (baseline_source_bitmap_bounded entry fuel)

/-- Removal fuel after the raw-call stage, now affine instead of geometric. -/
noncomputable def baselineRemovedAffineFuel (fuel : Nat) : Nat := baselineRawFuel fuel +
  baselineBitmapScale * ((2 * baselineRemovalLimit + 2) * baselineRawFuel fuel + 2 * baselineRemovalLimit) + 1

/-- Native fuel from Word entry fuel with the affine stack-removal stage. The
Word-to-Stack stage (baselineWordFuel) is still the geometric ceiling. -/
noncomputable def baselineNativeAffineRemovalFuel (fuel : Nat) : Nat :=
  14467153 * ((2 * baselineNamedLimit + 3) * baselineRemovedAffineFuel fuel + 4 * baselineNamedLimit)

theorem baseline_word_return_native_affine_removal {input : Guest.InputBlob}
    (entry : BaselineRuntimeEntry input) (fuel : Nat)
    (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory)
    (values : List (WordLocW 64))
    (run : WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {entryWordState entry.cfg entry.source with clock := fuel} = (some (.result (.loc 1 0) values), wordPost)) :
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeAffineRemovalFuel fuel ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt outcome, native, final.ffi) ∧
      ((outcome = .success ∧ final.ffi = wordPost.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents wordPost.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨wc,rc,mc,lc,final,outcome,count,native,wb,rb,mb,lb,nb,evaluated,observation⟩ :=
    baseline_word_return_native_affine_path entry fuel wordPost values run
  have word := baseline_wordWork_ceiling entry fuel
  have removal := baseline_removeAffineWork_bound entry rc
  have wordCap : wc ≤ baselineWordFuel fuel := by unfold baselineWordFuel; omega
  have rawCap : rc ≤ baselineRawFuel fuel := by unfold baselineRawFuel; omega
  have growth := Nat.mul_le_mul_left baselineBitmapScale
    (Nat.add_le_add_right (Nat.mul_le_mul_left (2 * baselineRemovalLimit + 2) rawCap) (2 * baselineRemovalLimit))
  have removedCap : mc ≤ baselineRemovedAffineFuel fuel := by unfold baselineRemovedAffineFuel; omega
  have scaled := Nat.mul_le_mul_left (2 * baselineNamedLimit + 3) removedCap
  have labels : mc - 1 + lc ≤ (2 * baselineNamedLimit + 3) * baselineRemovedAffineFuel fuel + 4 * baselineNamedLimit := by
    have localBound : mc - 1 + lc ≤ (2 * baselineNamedLimit + 3) * mc + 4 * baselineNamedLimit := by
      rw [show 2 * baselineNamedLimit + 3 = (2 * baselineNamedLimit + 2) + 1 by omega, Nat.add_mul, Nat.one_mul]
      omega
    exact Nat.le_trans localBound (Nat.add_le_add_right scaled _)
  have nativeCap := Nat.mul_le_mul_left 14467153 labels
  exact ⟨final,outcome,count,native,Nat.le_trans nb nativeCap,evaluated,observation⟩

#print axioms baseline_removeAffineWork_bound
#print axioms baseline_word_return_native_affine_removal
end InitECandidate.Runtime
