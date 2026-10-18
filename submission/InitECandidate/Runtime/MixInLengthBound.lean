import InitECandidate.Runtime.OriginalMixInLengthCode
import InitECandidate.Runtime.Sha256PairBound
import InitECandidate.Runtime.VmFn_st_le64
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem mixInLength_funBounded : FunBounded (ofString "mix_in_length") 155 :=
  ⟨_,_,_,originalRuntimeCode_mixInLength_lookup,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · vm_bound [sha256Pair_funBounded,vmBound_st_le64]
    · decide⟩

#print axioms mixInLength_funBounded
end InitECandidate.Runtime
