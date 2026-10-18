import InitECandidate.Runtime.CanonicalMainInput
import InitECandidate.Runtime.MainInitializationBuffersReach
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- The canonical original main reaches its zero-buffer setup with the
actual input and output allocations, or terminates within the same bound. -/
theorem canonical_main_buffers (input : Guest.InputBlob) (fuel : Nat)
    (budget : (1893 + (inputBlobBodyCost + 1)) + 4 ≤ fuel) :
    let state := {canonicalOriginalSourceEntry input with clock := fuel}
    Reaches state (mainAt 0) (MainBuffersReady state)
      ((1893 + (inputBlobBodyCost + 1)) + 4) (mainAt 17) := by
  apply main_initialization_buffers_reaches
  · exact canonical_original_source_code input
  · exact budget
  · exact canonical_main_input input fuel (by omega)

#print axioms canonical_main_buffers
end InitECandidate.Runtime
