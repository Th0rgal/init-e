import InitECandidate.Runtime.CanonicalOriginalNativeAffine
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE InitECandidate.Proofs Flapjack Flapjack.Compiler.Backend Flapjack.Compiler.Encoders.RiscV.Target

theorem affine_step (c d a b x y : Nat) (h : y ≤ a * x + b) : c * y + d ≤ (c * a) * x + (c * b + d) := by
  have scaled := Nat.mul_le_mul_left c h
  rw [Nat.mul_add, ← Nat.mul_assoc] at scaled
  omega

/-- Abstract affine chain over arbitrary stage constants (C crep limit, W word
limit, S bitmap scale, R removal limit, N named limit, K native factor). -/
theorem affine_chain (C W S R N K fuel : Nat) :
    let x := fuel + 1 + ((5 * C + 5) * (fuel + 1) + 2 * C)
    let word := x + ((2 * W + 2) * x + 2 * W)
    let raw := 2 * word
    let removed := raw + S * ((2 * R + 2) * raw + 2 * R) + 1
    K * ((2 * N + 3) * removed + 4 * N) ≤
      (K * (2 * N + 3) * ((1 + S * (2 * R + 2)) * (2 * ((1 + (2 * W + 2)) * (1 + (5 * C + 5)))))) * fuel +
      (K * (2 * N + 3) * ((1 + S * (2 * R + 2)) * (2 * ((1 + (2 * W + 2)) * (1 + (5 * C + 5) + 2 * C) + 2 * W) + 0) +
        (S * (2 * R) + 1)) + K * (4 * N)) := by
  intro x word raw removed
  have hx : x ≤ (1 + (5 * C + 5)) * fuel + (1 + (5 * C + 5) + 2 * C) := by
    simp only [x, Nat.mul_add, Nat.add_mul, Nat.mul_one, Nat.one_mul]
    omega
  have hw : word ≤ (1 + (2 * W + 2)) * x + 2 * W := by
    simp only [word, Nat.add_mul, Nat.one_mul]
    omega
  have wordC := Nat.le_trans hw (affine_step (1 + (2 * W + 2)) (2 * W) _ _ fuel x hx)
  have rawC : raw ≤ (2 * ((1 + (2 * W + 2)) * (1 + (5 * C + 5)))) * fuel +
      (2 * ((1 + (2 * W + 2)) * (1 + (5 * C + 5) + 2 * C) + 2 * W) + 0) :=
    affine_step 2 0 _ _ fuel word wordC
  have hr : removed ≤ (1 + S * (2 * R + 2)) * raw + (S * (2 * R) + 1) := by
    simp only [removed, Nat.mul_add, Nat.add_mul, Nat.one_mul, ← Nat.mul_assoc]
    omega
  have removedC := Nat.le_trans hr (affine_step (1 + S * (2 * R + 2)) (S * (2 * R) + 1) _ _ fuel raw rawC)
  have native := affine_step (K * (2 * N + 3)) (K * (4 * N)) _ _ fuel removed removedC
  have shape : K * ((2 * N + 3) * removed + 4 * N) = K * (2 * N + 3) * removed + K * (4 * N) := by
    rw [Nat.mul_add, Nat.mul_assoc]
  rw [shape]
  exact native

/-- Slope and offset of the whole original-source-fuel to native-step bound. -/
noncomputable def sourceNativeSlope : Nat :=
  (14467153 * (2 * baselineNamedLimit + 3) * ((1 + baselineBitmapScale * (2 * baselineRemovalLimit + 2)) *
    (2 * ((1 + (2 * baselineWordLimit + 2)) * (1 + (5 * baselineCrepLimit + 5))))))
noncomputable def sourceNativeOffset : Nat :=
  (14467153 * (2 * baselineNamedLimit + 3) * ((1 + baselineBitmapScale * (2 * baselineRemovalLimit + 2)) *
    (2 * ((1 + (2 * baselineWordLimit + 2)) * (1 + (5 * baselineCrepLimit + 5) + 2 * baselineCrepLimit) +
      2 * baselineWordLimit) + 0) + (baselineBitmapScale * (2 * baselineRemovalLimit) + 1)) +
    14467153 * (4 * baselineNamedLimit))

/-- The composed native budget is bounded by one explicit affine function of
the original Pancake source fuel. -/
theorem sourceNativeFuel_affine (fuel : Nat) :
    baselineNativeAffineFuel (fuel + 1 + baselineCrepAffineExtraFuel (fuel + 1)) ≤
      sourceNativeSlope * fuel + sourceNativeOffset :=
  affine_chain baselineCrepLimit baselineWordLimit baselineBitmapScale baselineRemovalLimit
    baselineNamedLimit 14467153 fuel

/-- Normal original-source return: native steps ≤ sourceNativeSlope*fuel + sourceNativeOffset. -/
theorem canonical_original_return_native_closed (input : Guest.InputBlob)
    (fuel : Nat) (post : PanSemStateFiniteExact 64 Guest.HostMemory) (value : ValueHOL 64)
    (run : ({canonicalOriginalSourceEntry input with clock := fuel} : PanSemStateFiniteExact 64 Guest.HostMemory).evaluateHOLFiniteState
      (.call none FrontendStages.Declarations.globalStart []) = (some (.returned value),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ sourceNativeSlope * fuel + sourceNativeOffset ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .success ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨wordPost, final, outcome, count, native, bound, rest⟩ :=
    canonical_original_return_native_affine input fuel post value run
  exact ⟨wordPost, final, outcome, count, native, Nat.le_trans bound (sourceNativeFuel_affine fuel), rest⟩

/-- Final-FFI original-source outcome within the same affine native bound. -/
theorem canonical_original_ffi_native_closed (input : Guest.InputBlob)
    (fuel : Nat) (post : PanSemStateFiniteExact 64 Guest.HostMemory) (event : HolFinalEvent)
    (run : ({canonicalOriginalSourceEntry input with clock := fuel} : PanSemStateFiniteExact 64 Guest.HostMemory).evaluateHOLFiniteState
      (.call none FrontendStages.Declarations.globalStart []) = (some (.finalFfi event),post)) :
    ∃ (wordPost : WordSemStateFiniteExact 64 (Nat × LabToTarget.Config) Guest.HostMemory),
    ∃ (final : LabSem.State 64 LabToTarget.Config Guest.HostMemory), ∃ outcome count native,
      count ≤ sourceNativeSlope * fuel + sourceNativeOffset ∧
      evaluateTargetHOL baselineMachineConfig (sourceFfi input) count baselineInstalledState =
        (.halt outcome,native,final.ffi) ∧
      ((outcome = .ffiOutcome event ∧ final.ffi = post.ffi) ∨
        (outcome = .resourceLimitHit ∧ List.IsPrefix final.ffi.ioEvents post.ffi.ioEvents ∧
          wordPost.stackMax.getD (wordPost.stackLimit + 1) > wordPost.stackLimit)) := by
  obtain ⟨wordPost, final, outcome, count, native, bound, rest⟩ :=
    canonical_original_ffi_native_affine input fuel post event run
  exact ⟨wordPost, final, outcome, count, native, Nat.le_trans bound (sourceNativeFuel_affine fuel), rest⟩

#print axioms sourceNativeFuel_affine
#print axioms canonical_original_return_native_closed
#print axioms canonical_original_ffi_native_closed
end InitECandidate.Runtime
