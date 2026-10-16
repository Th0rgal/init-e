import InitECandidate.Runtime.StackPathAffine
import InitECandidate.Runtime.BaselineStackEntryCeiling
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
namespace InitECandidate.Runtime
open InitE Flapjack
open Flapjack.Compiler.Backend.StackLang

/-- Every procedure of the actual named baseline code has the affine
StackToLab simulation, with static size and oracle bounds proved internally. -/
theorem baseline_named_affine_simulation {input : Guest.InputBlob}
    (entry : BaselineRuntimeEntry input) (fuel key : Nat) (body : HolProg 64)
    (lookup : sptLookup key (entryNamedState entry fuel).code = some body) :
    StackToLab.BoundedFlattenProp body (entryNamedState entry fuel)
      ((2 * baselineNamedLimit + 2) * fuel + 2 * baselineNamedLimit) := by
  have bounded := entryNamedState_bounded entry fuel
  exact StackToLab.flatten_program_affine baselineNamedLimit body (entryNamedState entry fuel)
    (bounded.code key body lookup) bounded

/-- Its stronger work bound charges actual consumed clock and current syntax. -/
theorem baseline_named_affine_work {input : Guest.InputBlob}
    (entry : BaselineRuntimeEntry input) (fuel key : Nat) (body : HolProg 64)
    (lookup : sptLookup key (entryNamedState entry fuel).code = some body) :
    StackToLab.AffinePathBound (2 * baselineNamedLimit + 2) body (entryNamedState entry fuel) := by
  have bounded := entryNamedState_bounded entry fuel
  exact StackToLab.pathWork_affine baselineNamedLimit body (entryNamedState entry fuel)
    (bounded.code key body lookup) bounded

#print axioms baseline_named_affine_simulation
#print axioms baseline_named_affine_work
end InitECandidate.Runtime
