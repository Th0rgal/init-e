import InitECandidate.Runtime.BaselineSourceAffineTransfer
import InitECandidate.Proofs.BaselineSubmission
namespace InitECandidate.Runtime
open InitE

/-- The concrete submitted compiler and bootstrap discharge the compiler side
of the finite-score certificate. A uniform source-runtime bound remains explicit. -/
theorem baseline_finite_certificate_of_source_bound (bound : Guest.InputBlob → Nat) (ceiling : Nat)
    (source : SourceBound bound)
    (uniform : ∀ input, Guest.GasLimit.declaredGasLimit input ≤ 200000000 → bound input ≤ ceiling) :
    Certificate (withScore baselineSubmission (.finite (sourceNativeSlope * ceiling + (sourceNativeOffset + 46240))))
      (.finite (sourceNativeSlope * ceiling + (sourceNativeOffset + 46240))) :=
  finite_certificate_of_bounds baselineSubmission sourceNativeSlope (sourceNativeOffset + 46240)
    ceiling bound baselineSubmission_admitted source uniform baseline_source_affine_transfer

#print axioms baseline_finite_certificate_of_source_bound
end InitECandidate.Runtime
