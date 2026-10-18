import InitECandidate.Runtime.VmSearch
import InitECandidate.Runtime.OriginalSha256FinishCode
import InitECandidate.Runtime.ForkInitSuffixBound
import InitECandidate.Runtime.Bn254InitBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem sha256Finish_funBounded' : FunBounded (ofString "sha256_finish") 16 :=
  ⟨_,_,_,originalRuntimeCode_sha256Finish_lookup,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound [storeBE32_funBounded]
    · decide⟩

theorem bn254Init_funBounded' : FunBounded (ofString "bn254_init") 34 :=
  ⟨_,_,_,originalRuntimeCode_bn254Init_lookup,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound [bn254AccelInit_funBounded,fqMul_funBounded,fqNeg_funBounded]
    · decide⟩

#print axioms sha256Finish_funBounded'
end InitECandidate.Runtime
