import InitECandidate.Runtime.ExpandedMainInitializers
import InitECandidate.Runtime.MainInitializationInputReach
namespace InitECandidate.Runtime
open InitE Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact

/-- Initialization and input loading of the enlarged-domain proof source,
from its real canonical entry, reach output-buffer setup or terminate early. -/
theorem expanded_main_input (input : Guest.InputBlob) (fuel : Nat)
    (budget : 1893 + (inputBlobBodyCost + 1) ≤ fuel) :
    let state := {expandedRuntimeEntry input with clock := fuel}
    Reaches state (mainAt 0) (MainInputReady state)
      (1893 + (inputBlobBodyCost + 1)) (mainAt 15) := by
  apply main_initialization_input_reaches
  · exact canonical_original_source_code input
  · exact budget
  · exact expanded_main_initializers input fuel (by omega)

#print axioms expanded_main_input
end InitECandidate.Runtime
