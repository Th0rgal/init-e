import InitECandidate.Runtime.VersionedHashesBodyAllocationFailureBound
import InitECandidate.Runtime.VersionedHashesCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The actual validation call adds one tick to the exhausted-heap body bound.
No readable input/header/slice or successful-allocation reserve is assumed. -/
theorem evaluate_versioned_hashes_call_allocation_failure_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (destination : Option (VarKind × MlS)) (arguments : List (ExpHOL 64)) (si heap : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments = some [.val (.word si)])
    (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (request : ((33806089496 : BitVec 64) - heap).toNat < 400) (budget : 6 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (.call (some (destination,none)) (ofString "is_valid_versioned_hashes") arguments)
    state.clock ≤ evaluated.2.clock + 6 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let callee : HolFiniteMapExact MlS (ValueHOL 64) := HolFiniteMapExact.empty.update (ofString "si",.val (.word si))
  let entry := callEntryStateHOLFinite state callee
  have bounded := evaluate_versioned_hashes_body_allocation_failure_bounded entry heap code heapGlobal request
    (by change 5 ≤ state.clock - 1; omega)
  have installed : state.code.lookup (ofString "is_valid_versioned_hashes") =
      some ([(ofString "si",.one)],sourceFunctionBody Guest.guestFn_is_valid_versioned_hashes,.one) := by
    rw [code]; exact originalRuntimeCode_versionedHashes_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "is_valid_versioned_hashes") (ofString "si")
    (sourceFunctionBody Guest.guestFn_is_valid_versioned_hashes) si installed
  cases bodyRun : evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_is_valid_versioned_hashes) with
  | mk result post =>
    rw [bodyRun] at bounded
    dsimp only at bounded
    have output := evaluate_call_body_clock_no_timeout state post (ofString "is_valid_versioned_hashes") destination arguments _
      (sourceFunctionBody Guest.guestFn_is_valid_versioned_hashes) callee .one result args lookup (by omega) bodyRun bounded.2.2
    dsimp only
    rw [output.2]
    refine ⟨?_,?_,output.1⟩
    · have spent := bounded.1
      change state.clock - 1 ≤ post.clock + 5 at spent
      change state.clock ≤ post.clock + 6
      omega
    · have remaining := bounded.2.1
      change post.clock ≤ state.clock - 1 at remaining
      change post.clock ≤ state.clock
      omega

#print axioms evaluate_versioned_hashes_call_allocation_failure_bounded
end InitECandidate.Runtime
