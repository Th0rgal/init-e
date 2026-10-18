import InitECandidate.Runtime.CountedLoop
import InitECandidate.Runtime.OriginalSha256FinishCode
import InitECandidate.Runtime.ForkInitSuffixBound
import InitECandidate.Runtime.AllocationInitializersBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- The original sha256_finish (8 counted st_be32 calls) costs at most 16 ticks. -/
theorem sha256Finish_funBounded : FunBounded (ofString "sha256_finish") 16 :=
  ⟨_,_,_,originalRuntimeCode_sha256Finish_lookup,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · apply ProgBounded.countedDec (ofString "i") .less (Or.inl rfl) 8 1 0 (by decide) (by decide) (by decide)
      · apply CountedBody.seq _ (ProgBounded.call storeBE32_funBounded _ _) (by decide) (by decide)
        exact CountedBody.incr
      · exact ProgBounded.straight _ (by decide)
    · decide⟩

#print axioms sha256Finish_funBounded
end InitECandidate.Runtime
