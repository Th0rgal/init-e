import InitECandidate.Runtime.MainAllInitializers
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem allInitializerGlobals_ssz_offsets (globals : HolFiniteMapExact MlS (ValueHOL 64)) :
    (allInitializerGlobals globals).lookup (ofString "ssz_offs") = some (.val (.word 2713715344)) := by
  unfold allInitializerGlobals lastFiveInitializerGlobals headerEvmForkInitializerGlobals evmForkInitializerGlobals
  rw [globalAllocationGlobals_lookup_other _ _ _ _ (by decide) (by decide),
    globalAllocationGlobals_lookup_other _ _ _ _ (by decide) (by decide)]
  rw [headerInitGlobals,globalAllocationGlobals_lookup_other _ _ _ _ (by decide) (by decide)]
  rw [ripemdBlakeInitializerGlobals,blake2InitGlobals_lookup_other _ _ _ (by decide) (by decide),
    globalAllocationGlobals_lookup_other _ _ _ _ (by decide) (by decide)]
  rw [firstNineInitializerGlobals,blsInitGlobals_lookup_other _ _ _ (by decide) (by decide),
    firstEightInitializerGlobals,bn254InitGlobals_other _ _ _ (by decide) (by decide)]
  simp only [firstSevenInitializerGlobals,secpInitActualGlobals,HolFiniteMapExact.lookup_update,FUPDATE]
  rw [firstSixInitializerGlobals,
    globalAllocationGlobals_lookup_other _ _ _ _ (by decide) (by decide),
    globalAllocationGlobals_lookup_other _ _ _ _ (by decide) (by decide)]
  simp [firstFourInitializerGlobals,globalAllocationGlobals,sszInitAllocations,
    HolFiniteMapExact.lookup_update,FUPDATE,ofString]
  decide

#print axioms allInitializerGlobals_ssz_offsets
end InitECandidate.Runtime
