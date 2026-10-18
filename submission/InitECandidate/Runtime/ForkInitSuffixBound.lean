import InitECandidate.Runtime.AddressFromWordsBound
import InitECandidate.Runtime.InitializerCounterSource
import InitECandidate.Runtime.AllocationInitializersBound
import InitECandidate.Runtime.ProgBounded
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem storeBE32_funBounded : FunBounded (ofString "st_be32") 0 :=
  ⟨_,_,_,originalRuntimeCode_storeBE32_lookup,by
    apply ProgBounded.straight
    simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
    rfl⟩

theorem storeBE64_funBounded : FunBounded (ofString "st_be64") 3 :=
  ⟨_,_,_,originalRuntimeCode_storeBE64_lookup,by
    intro F state code budget
    exact evaluate_storeBE64_body_bounded state code budget⟩

theorem addressFromWords_funBounded : FunBounded (ofString "addr_from_words") 9 :=
  ⟨_,_,_,originalRuntimeCode_addressFromWords_lookup,by
    intro F state code budget
    exact evaluate_addressFromWords_body_bounded state code budget⟩

def forkInitStructuralAt : Nat → ProgHOL 64
  | 0 => structuralFunctionBody Guest.guestFn_fork_init
  | n + 1 => statelessNext (forkInitStructuralAt n)

theorem forkInitAt_eq_structural (index : Nat) : forkInitAt index = forkInitStructuralAt index := by
  induction index with
  | zero => exact sourceFunctionBody_eq_structural Guest.guestFn_fork_init
  | succ index ih => simp only [forkInitAt,forkInitStructuralAt,ih]

/-- Eight allocator calls, seven address encodings and four 64-bit stores
bound the actual suffix after the precompile counter loop. -/
theorem forkInit_suffix_structural_bounded : ProgBounded (forkInitStructuralAt 6) 102 := by
  apply ProgBounded.weaken
  · repeat first
      | exact ProgBounded.straight _ (by decide)
      | apply ProgBounded.seq
      | exact ProgBounded.alloc _ _
      | exact ProgBounded.call addressFromWords_funBounded _ _
      | exact ProgBounded.call storeBE64_funBounded _ _
  · decide

theorem evaluate_forkInit_suffix_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (code : state.code = originalRuntimeCode) (budget : 102 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (forkInitAt 6)
    state.clock ≤ evaluated.2.clock + 102 ∧ evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  rw [forkInitAt_eq_structural]
  exact forkInit_suffix_structural_bounded state code budget

#print axioms storeBE32_funBounded
#print axioms storeBE64_funBounded
#print axioms addressFromWords_funBounded
#print axioms forkInitAt_eq_structural
#print axioms evaluate_forkInit_suffix_bounded
end InitECandidate.Runtime
