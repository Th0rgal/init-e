import InitECandidate.Runtime.NestedCountedLoop
import InitECandidate.Runtime.OriginalSha256BlockCode
import InitECandidate.Runtime.MemConstCallBound
import InitECandidate.Runtime.AllocationInitializersBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

/-- Original block hashing has two four-iteration loops and one optional
64-byte copy. The accelerator call and rejection outcomes are covered. -/
theorem sha256Block_funBounded : FunBounded (ofString "sha256_block") 29 :=
  ⟨_,_,_,originalRuntimeCode_sha256Block_lookup,by
    rw [sourceFunctionBody_eq_structural]
    apply ProgBounded.weaken
    · apply ProgBounded.seq
      · apply ProgBounded.ite
        · exact memcpy_const_progBounded _ _ 64 (by decide)
        · exact ProgBounded.weaken (ProgBounded.straight _ (by decide)) (Nat.zero_le _)
      · apply ProgBounded.nestedCountedDec (ofString "i") .less (Or.inl rfl) 4 1 0
          (by decide) (by decide) (by decide)
        · apply NestedCountedBody.dec _ _ _ (by decide)
          apply NestedCountedBody.dec _ _ _ (by decide)
          apply NestedCountedBody.base
          apply CountedBody.seq _ (ProgBounded.straight _ (by decide)) (by decide) (by decide)
          exact CountedBody.incr
        · apply ProgBounded.seq
          · exact ProgBounded.straight _ (by decide)
          · apply ProgBounded.nestedCountedAssign (ofString "i") .less (Or.inl rfl) 4 1 0
              (by decide) (by decide) (by decide)
            · apply NestedCountedBody.dec _ _ _ (by decide)
              apply NestedCountedBody.base
              apply CountedBody.seq _ (ProgBounded.straight _ (by decide)) (by decide) (by decide)
              apply CountedBody.seq _ (ProgBounded.straight _ (by decide)) (by decide) (by decide)
              exact CountedBody.incr
            · exact ProgBounded.straight _ (by decide)
    · decide⟩

#print axioms sha256Block_funBounded
end InitECandidate.Runtime
