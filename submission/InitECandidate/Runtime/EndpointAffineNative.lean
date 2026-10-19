import InitECandidate.Runtime.EndpointWordCeiling
import InitECandidate.Runtime.EndpointWordNativeFullAffine
import InitECandidate.Runtime.EndpointRemovalAffineNative
import InitECandidate.Runtime.BaselineAffineNative
import InitECandidate.Runtime.BaselineWordCeiling
import InitECandidate.Runtime.BaselineWordNativeFullAffine
import InitECandidate.Runtime.BaselineRemovalAffineNative
import InitECandidate.Runtime.WordPathAffine
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs
open Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target
open Flapjack.Compiler.Backend.StackToLab.Proofs.FullMakeInitSemantics

/-- Actual baseline WordToStack overhead is affine in the Word entry fuel. -/
theorem endpoint_wordPathWork_affine {input : Guest.InputBlob}
    (entry : EndpointRuntimeEntry input endpoint) (fuel : Nat) :
    WordToStack.wordPathWork (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {entryWordState entry.cfg entry.source with clock := fuel} ≤
      (2 * baselineWordLimit + 2) * fuel + 2 * baselineWordLimit :=
  WordToStack.wordPathWork_affine_fuel baselineWordLimit _ _ (Nat.le_max_left _ _)
    (endpointWordState_bounded entry fuel) rfl

/-- Stage clocks produced by the affine chain compose to the fixed native budget. -/
theorem endpoint_affine_fuel_compose {input : Guest.InputBlob}
    (entry : EndpointRuntimeEntry input endpoint) (fuel wc rc mc lc count : Nat)
    (wb : wc ≤ fuel + WordToStack.wordPathWork (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
        {entryWordState entry.cfg entry.source with clock := fuel})
    (rb : rc ≤ 2 * wc)
    (mb : mc ≤ rc + StackRemove.removeAffineWork (.call none (.inl BvlToBvi.initGlobalsLocation) none)
        {entry.source with clock := rc} + 1)
    (lb : lc ≤ (2 * baselineNamedLimit + 2) * mc + 4 * baselineNamedLimit)
    (nb : count ≤ 14467153 * (mc - 1 + lc)) :
    count ≤ baselineNativeAffineFuel fuel := by
  have word := endpoint_wordPathWork_affine entry fuel
  have removal := endpoint_removeAffineWork_bound entry rc
  have wordCap : wc ≤ baselineWordAffineFuel fuel := by unfold baselineWordAffineFuel; omega
  have rawCap : rc ≤ baselineRawAffineFuel fuel := by unfold baselineRawAffineFuel; omega
  have growth := Nat.mul_le_mul_left baselineBitmapScale
    (Nat.add_le_add_right (Nat.mul_le_mul_left (2 * baselineRemovalLimit + 2) rawCap) (2 * baselineRemovalLimit))
  have removedCap : mc ≤ baselineRemovedFullAffineFuel fuel := by unfold baselineRemovedFullAffineFuel; omega
  have scaled := Nat.mul_le_mul_left (2 * baselineNamedLimit + 3) removedCap
  have labels : mc - 1 + lc ≤ (2 * baselineNamedLimit + 3) * baselineRemovedFullAffineFuel fuel + 4 * baselineNamedLimit := by
    have localBound : mc - 1 + lc ≤ (2 * baselineNamedLimit + 3) * mc + 4 * baselineNamedLimit := by
      rw [show 2 * baselineNamedLimit + 3 = (2 * baselineNamedLimit + 2) + 1 by omega, Nat.add_mul, Nat.one_mul]
      omega
    exact Nat.le_trans localBound (Nat.add_le_add_right scaled _)
  exact Nat.le_trans nb (Nat.mul_le_mul_left 14467153 labels)

/-- Normal Word entry return reaches installed native halt within the affine budget. -/
theorem endpoint_word_return_native_affine_bound {input : Guest.InputBlob}
    (entry : EndpointRuntimeEntry input endpoint) (fuel : Nat)
    (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory)
    (values : List (WordLocW 64))
    (run : WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {entryWordState entry.cfg entry.source with clock := fuel} = (some (.result (.loc 1 0) values), wordPost)) :
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeAffineFuel fuel ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count endpoint =
        (.halt outcome, native, final.ffi) ∧
      ((outcome = .success ∧ final.ffi = wordPost.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents wordPost.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨wc,rc,mc,lc,final,outcome,count,native,wb,rb,mb,lb,nb,evaluated,observation⟩ :=
    endpoint_word_return_native_affine_full entry fuel wordPost values run
  exact ⟨final,outcome,count,native,endpoint_affine_fuel_compose entry fuel wc rc mc lc count wb rb mb lb nb,
    evaluated,observation⟩

/-- Final-FFI Word outcome within the same affine native budget. -/
theorem endpoint_word_ffi_native_affine_bound {input : Guest.InputBlob}
    (entry : EndpointRuntimeEntry input endpoint) (fuel : Nat)
    (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory)
    (event : HolFinalEvent)
    (run : WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {entryWordState entry.cfg entry.source with clock := fuel} = (some (.finalFfi event), wordPost)) :
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ baselineNativeAffineFuel fuel ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count endpoint =
        (.halt outcome, native, final.ffi) ∧
      ((outcome = .ffiOutcome event ∧ final.ffi = wordPost.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents wordPost.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨wc,rc,mc,lc,final,outcome,count,native,wb,rb,mb,lb,nb,evaluated,observation⟩ :=
    endpoint_word_ffi_native_affine_full entry fuel wordPost event run
  exact ⟨final,outcome,count,native,endpoint_affine_fuel_compose entry fuel wc rc mc lc count wb rb mb lb nb,
    evaluated,observation⟩

/-- Word notEnoughSpace outcome reaches the native resource-limit halt within the affine budget. -/
theorem endpoint_word_resource_native_affine_bound {input : Guest.InputBlob}
    (entry : EndpointRuntimeEntry input endpoint) (fuel : Nat)
    (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory)
    (run : WordSemStateFiniteExact.evaluate (.call none (some BvlToBvi.initGlobalsLocation) [0] none)
      {entryWordState entry.cfg entry.source with clock := fuel} = (some .notEnoughSpace, wordPost)) :
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ count native,
      count ≤ baselineNativeAffineFuel fuel ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count endpoint =
        (.halt .resourceLimitHit, native, final.ffi) ∧
      (final.ffi = wordPost.ffi ∨
        (List.IsPrefix final.ffi.ioEvents wordPost.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨wc,rc,mc,lc,final,count,native,wb,rb,mb,lb,nb,evaluated,observation⟩ :=
    endpoint_word_resource_native_affine_full entry fuel wordPost run
  exact ⟨final,count,native,endpoint_affine_fuel_compose entry fuel wc rc mc lc count wb rb mb lb nb,
    evaluated,observation⟩

#print axioms endpoint_wordPathWork_affine
#print axioms endpoint_affine_fuel_compose
#print axioms endpoint_word_return_native_affine_bound
#print axioms endpoint_word_ffi_native_affine_bound
#print axioms endpoint_word_resource_native_affine_bound
end InitECandidate.Runtime
