import InitECandidate.Runtime.MainAllInitializers
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem allInitializerGlobals_sha_state (globals : HolFiniteMapExact MlS (ValueHOL 64)) :
    (allInitializerGlobals globals).lookup (ofString "sha_st") = some (.val (.word 2713714688)) := by
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
  simp [firstFourInitializerGlobals,globalAllocationGlobals,sszInitAllocations,sha256InitAllocations,keccakInitAllocations,
    HolFiniteMapExact.lookup_update,FUPDATE,ofString]
  all_goals decide

theorem allInitializerGlobals_sha_accelerator (globals : HolFiniteMapExact MlS (ValueHOL 64)) :
    (allInitializerGlobals globals).lookup (ofString "sha_accel") = some (.val (.word 2713714880)) := by
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
  simp [firstFourInitializerGlobals,globalAllocationGlobals,sszInitAllocations,sha256InitAllocations,keccakInitAllocations,
    HolFiniteMapExact.lookup_update,FUPDATE,ofString]
  all_goals decide

theorem allInitializerGlobals_ssz_chunk (globals : HolFiniteMapExact MlS (ValueHOL 64)) :
    (allInitializerGlobals globals).lookup (ofString "ssz_len_chunk") = some (.val (.word 2713715312)) := by
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
  simp [firstFourInitializerGlobals,globalAllocationGlobals,sszInitAllocations,sha256InitAllocations,keccakInitAllocations,
    HolFiniteMapExact.lookup_update,FUPDATE,ofString]
  all_goals decide

theorem allInitializerGlobals_zero_hashes (globals : HolFiniteMapExact MlS (ValueHOL 64)) :
    (allInitializerGlobals globals).lookup (ofString "zero_hashes") = some (.val (.word 2713715408)) := by
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
  simp [firstFourInitializerGlobals,globalAllocationGlobals,sszInitAllocations,sha256InitAllocations,keccakInitAllocations,
    HolFiniteMapExact.lookup_update,FUPDATE,ofString]
  all_goals decide

#print axioms allInitializerGlobals_sha_state
#print axioms allInitializerGlobals_sha_accelerator
#print axioms allInitializerGlobals_ssz_chunk
#print axioms allInitializerGlobals_zero_hashes
end InitECandidate.Runtime
