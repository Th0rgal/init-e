import InitECandidate.Runtime.SourceCostEntryPayload
import InitE.SourceDeclarationsCore
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option cbv.maxSteps 1000000000
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang

/-- Every source function named `main` returns one well-formed word. -/
theorem guest_source_main_return :
    (functionsHOL InitE.sourceDeclarations).all (fun entry =>
      entry.1 != Flapjack.Basis.Pure.MlString.ofString "main" ||
        (isWfShapeExactHOL ([] : StructContextExact) entry.2.2.2 && decide (sizeOfShapeHOL entry.2.2.2 ≤ 1))) =
      true := by
  decide_cbv

/-- Every declared exception carries one well-formed word. -/
theorem guest_source_exn_shapes :
    (exceptionsHOL InitE.sourceDeclarations).all (fun entry =>
      isWfShapeExactHOL ([] : StructContextExact) entry.2 && decide (sizeOfShapeHOL entry.2 ≤ 1)) = true := by
  decide_cbv

#print axioms guest_source_main_return
#print axioms guest_source_exn_shapes
end InitECandidate.Runtime.FineCost
