import InitECandidate.Runtime.PtWsFloorGD
import InitECandidate.Runtime.MainAllInitializers
/-!
The workspace globals after all initializers of the actual main (`allInitializerGlobals`): the keccak state, padding
and nibble scratch keep the values installed by the first six initializers.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem allInitializerGlobals_nib (globals : HolFiniteMapExact MlS (ValueHOL 64)) :
    (allInitializerGlobals globals).lookup (ofString "mpt_nib_scratch") = some (.val (.word 2713717520)) := by
  unfold allInitializerGlobals lastFiveInitializerGlobals headerEvmForkInitializerGlobals evmForkInitializerGlobals
  rw [globalAllocationGlobals_lookup_other _ _ _ _ (by decide) (by decide),
    globalAllocationGlobals_lookup_other _ _ _ _ (by decide) (by decide)]
  rw [headerInitGlobals,globalAllocationGlobals_lookup_other _ _ _ _ (by decide) (by decide)]
  rw [ripemdBlakeInitializerGlobals,blake2InitGlobals_lookup_other _ _ _ (by decide) (by decide),
    globalAllocationGlobals_lookup_other _ _ _ _ (by decide) (by decide)]
  rw [firstNineInitializerGlobals,blsInitGlobals_lookup_other _ _ _ (by decide) (by decide),
    firstEightInitializerGlobals,bn254InitGlobals_other _ _ _ (by decide) (by decide)]
  simp only [firstSevenInitializerGlobals,secpInitActualGlobals,HolFiniteMapExact.lookup_update,FUPDATE]
  exact firstSixInitializerGlobals_nib globals

#print axioms allInitializerGlobals_nib

theorem allInitializerGlobals_keccak_st (globals : HolFiniteMapExact MlS (ValueHOL 64)) :
    (allInitializerGlobals globals).lookup (ofString "keccak_st") = some (.val (.word 2713714976)) := by
  unfold allInitializerGlobals lastFiveInitializerGlobals headerEvmForkInitializerGlobals evmForkInitializerGlobals
  rw [globalAllocationGlobals_lookup_other _ _ _ _ (by decide) (by decide),
    globalAllocationGlobals_lookup_other _ _ _ _ (by decide) (by decide)]
  rw [headerInitGlobals,globalAllocationGlobals_lookup_other _ _ _ _ (by decide) (by decide)]
  rw [ripemdBlakeInitializerGlobals,blake2InitGlobals_lookup_other _ _ _ (by decide) (by decide),
    globalAllocationGlobals_lookup_other _ _ _ _ (by decide) (by decide)]
  rw [firstNineInitializerGlobals,blsInitGlobals_lookup_other _ _ _ (by decide) (by decide),
    firstEightInitializerGlobals,bn254InitGlobals_other _ _ _ (by decide) (by decide)]
  simp only [firstSevenInitializerGlobals,secpInitActualGlobals,HolFiniteMapExact.lookup_update,FUPDATE]
  exact (firstSixInitializerGlobals_layout globals).2.2.2.2.1

#print axioms allInitializerGlobals_keccak_st

theorem allInitializerGlobals_keccak_pad (globals : HolFiniteMapExact MlS (ValueHOL 64)) :
    (allInitializerGlobals globals).lookup (ofString "keccak_pad") = some (.val (.word 2713715176)) := by
  unfold allInitializerGlobals lastFiveInitializerGlobals headerEvmForkInitializerGlobals evmForkInitializerGlobals
  rw [globalAllocationGlobals_lookup_other _ _ _ _ (by decide) (by decide),
    globalAllocationGlobals_lookup_other _ _ _ _ (by decide) (by decide)]
  rw [headerInitGlobals,globalAllocationGlobals_lookup_other _ _ _ _ (by decide) (by decide)]
  rw [ripemdBlakeInitializerGlobals,blake2InitGlobals_lookup_other _ _ _ (by decide) (by decide),
    globalAllocationGlobals_lookup_other _ _ _ _ (by decide) (by decide)]
  rw [firstNineInitializerGlobals,blsInitGlobals_lookup_other _ _ _ (by decide) (by decide),
    firstEightInitializerGlobals,bn254InitGlobals_other _ _ _ (by decide) (by decide)]
  simp only [firstSevenInitializerGlobals,secpInitActualGlobals,HolFiniteMapExact.lookup_update,FUPDATE]
  exact (firstSixInitializerGlobals_layout globals).2.2.2.2.2.1

#print axioms allInitializerGlobals_keccak_pad

end InitECandidate.Runtime
