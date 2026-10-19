import InitECandidate.Runtime.EndpointRemovalCeiling
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
theorem endpoint_removeAffineWork_bound {input : Guest.InputBlob}
    (entry : EndpointRuntimeEntry input endpoint) (fuel : Nat) :
    StackRemove.removeAffineWork (.call none (.inl BvlToBvi.initGlobalsLocation) none)
      {entry.source with clock := fuel} ≤
      baselineBitmapScale * ((2 * baselineRemovalLimit + 2) * fuel + 2 * baselineRemovalLimit) :=
  StackRemove.removeAffineWork_le baselineRemovalLimit baselineBitmapScale _ _
    (Nat.le_max_left _ _) (endpoint_source_code_bounded entry fuel)
    (endpoint_source_bitmap_bounded entry fuel)

#print axioms endpoint_removeAffineWork_bound
end InitECandidate.Runtime
