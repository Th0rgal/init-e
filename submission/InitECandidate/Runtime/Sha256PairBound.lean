import InitECandidate.Runtime.Sha256BlockBound
import InitECandidate.Runtime.OriginalSha256PairCode
import InitECandidate.Runtime.VmFn_sha256_state_init
import InitECandidate.Runtime.VmFn_sha256_finish
import InitECandidate.Runtime.VmFn_st_be64
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- The original two-chunk SHA-256 helper, including both accelerator blocks
and all fixed-size memory calls, costs at most 135 source ticks. -/
theorem sha256Pair_funBounded : FunBounded (ofString "sha256_pair") 135 :=
  ⟨_,_,_,originalRuntimeCode_sha256Pair_lookup,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound [vmBound_sha256_state_init,sha256Block_funBounded,vmBound_st_be64,vmBound_sha256_finish]
    · decide⟩

#print axioms sha256Pair_funBounded
end InitECandidate.Runtime
