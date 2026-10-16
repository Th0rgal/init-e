import InitECandidate.Runtime.BaselineWordCeiling
import InitECandidate.Runtime.BaselineWordNativeCeiling
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Compiler.Backend
open Flapjack.Compiler.Encoders.RiscV.Target

noncomputable def baselineWordFuel (fuel : Nat) : Nat := fuel + workCeiling baselineWordLimit fuel
  (sizeOf (.call none (some BvlToBvi.initGlobalsLocation) [0] none : WordLangProgHOL (BitVec 64)))
noncomputable def baselineRawFuel (fuel : Nat) : Nat := 2 * baselineWordFuel fuel
noncomputable def baselineRemovedFuel (fuel : Nat) : Nat := baselineRawFuel fuel +
  baselineBitmapScale * workCeiling baselineRemovalLimit (baselineRawFuel fuel)
    (sizeOf (.call none (.inl BvlToBvi.initGlobalsLocation) none : StackLang.HolProg 64)) + 1
noncomputable def baselineNativeFuel (fuel : Nat) : Nat :=
  14467153 * ((2 * baselineNamedLimit + 3) * baselineRemovedFuel fuel + 4 * baselineNamedLimit)

theorem workCeiling_fuel_mono (limit nodes a b : Nat) (less : a ≤ b) :
    workCeiling limit a nodes ≤ workCeiling limit b nodes := by
  apply Nat.pow_le_pow_right (by decide)
  have scaled := Nat.mul_le_mul_right (limit + 1) less
  unfold workRank
  omega

/-- A single explicit fixed-program function bounds native steps from Word
entry fuel. No dynamic work budget or recursive compiler premise remains. -/
theorem baseline_word_return_native_uniform {input : Guest.InputBlob}
    (entry : BaselineRuntimeEntry input) (fuel : Nat)
    (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory)
    (values : List (WordLocW 64))
    (run : WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {entryWordState entry.cfg entry.source with clock := fuel} = (some (.result (.loc 1 0) values), wordPost)) :
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeFuel fuel ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt outcome, native, final.ffi) ∧
      ((outcome = .success ∧ final.ffi = wordPost.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents wordPost.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨wc,rc,mc,lc,final,outcome,count,native,wb,rb,mb,lb,nb,evaluated,observation⟩ :=
    baseline_word_return_native_ceiling entry fuel wordPost values run
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

#print axioms baseline_word_return_native_uniform
end InitECandidate.Runtime
