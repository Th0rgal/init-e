import InitECandidate.Runtime.MainFirstFourInitializers
import InitECandidate.Runtime.MptInitSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def firstFourInitializerGlobals (globals : HolFiniteMapExact MlS (ValueHOL 64)) :
    HolFiniteMapExact MlS (ValueHOL 64) :=
  globalAllocationGlobals
    (globalAllocationGlobals
      (globalAllocationGlobals
        (((globals.update (ofString "heap_ptr",.val (.word 2713714688))).update
          (ofString "scratch_ptr",.val (.word 2713714688))).update
            (ofString "frame_mem_ptr",.val (.word 2701135872)))
        2713714688 sha256InitAllocations) 2713714976 keccakInitAllocations)
    2713715312 sszInitAllocations

theorem firstFourInitializerGlobals_keccak (globals : HolFiniteMapExact MlS (ValueHOL 64)) :
    (firstFourInitializerGlobals globals).lookup (ofString "keccak_st") = some (.val (.word 2713714976)) ∧
      (firstFourInitializerGlobals globals).lookup (ofString "keccak_pad") = some (.val (.word 2713715176)) := by
  simp [firstFourInitializerGlobals,globalAllocationGlobals,sha256InitAllocations,keccakInitAllocations,
    sszInitAllocations,HolFiniteMapExact.lookup_update,FUPDATE,ofString]
  decide

theorem firstFourInitializerGlobals_lookup_other (globals : HolFiniteMapExact MlS (ValueHOL 64))
    (key : MlS) (notHeap : key ≠ ofString "heap_ptr") (notScratch : key ≠ ofString "scratch_ptr")
    (notFrame : key ≠ ofString "frame_mem_ptr")
    (notSha : ∀ entry ∈ sha256InitAllocations, key ≠ entry.1)
    (notKeccak : ∀ entry ∈ keccakInitAllocations, key ≠ entry.1)
    (notSsz : ∀ entry ∈ sszInitAllocations, key ≠ entry.1) :
    (firstFourInitializerGlobals globals).lookup key = globals.lookup key := by
  rw [firstFourInitializerGlobals,
    globalAllocationGlobals_lookup_other _ _ _ _ notHeap notSsz,
    globalAllocationGlobals_lookup_other _ _ _ _ notHeap notKeccak,
    globalAllocationGlobals_lookup_other _ _ _ _ notHeap notSha]
  simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notHeap,Ne.symm notScratch,Ne.symm notFrame]

theorem firstFourInitializerGlobals_mpt_workspace (globals : HolFiniteMapExact MlS (ValueHOL 64)) :
    ∀ entry ∈ mptInitAllocations ++ [(ofString "u256_ws",0)],
      (firstFourInitializerGlobals globals).lookup entry.1 = globals.lookup entry.1 := by
  intro entry member
  have distinct : ∀ entry ∈ mptInitAllocations ++ [(ofString "u256_ws",0)],
      entry.1 ≠ ofString "heap_ptr" ∧ entry.1 ≠ ofString "scratch_ptr" ∧ entry.1 ≠ ofString "frame_mem_ptr" ∧
      (∀ other ∈ sha256InitAllocations, entry.1 ≠ other.1) ∧
      (∀ other ∈ keccakInitAllocations, entry.1 ≠ other.1) ∧
      (∀ other ∈ sszInitAllocations, entry.1 ≠ other.1) := by decide
  obtain ⟨a,b,c,d,e,f⟩ := distinct entry member
  exact firstFourInitializerGlobals_lookup_other globals entry.1 a b c d e f

#print axioms firstFourInitializerGlobals_keccak
#print axioms firstFourInitializerGlobals_lookup_other
#print axioms firstFourInitializerGlobals_mpt_workspace
end InitECandidate.Runtime
