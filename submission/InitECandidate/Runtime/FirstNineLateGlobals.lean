import InitECandidate.Runtime.MainFirstNineInitializers
import InitECandidate.Runtime.MainLastFiveInitializers
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

def remainingInitializerNames : List MlS :=
  ripemdInitAllocations.map Prod.fst ++ blakeInitializerNames ++ [ofString "hdr_zero8"] ++
    evmInitAllocations.map Prod.fst ++ forkInitAllocations.map Prod.fst

theorem blsInitGlobals_lookup_other (globals : HolFiniteMapExact MlS (ValueHOL 64))
    (pointer : BitVec 64) (key : MlS) (notHeap : key ≠ ofString "heap_ptr")
    (notWritten : key ∉ blsInitializerNames) :
    (blsInitGlobals globals pointer).lookup key = globals.lookup key := by
  simp only [blsInitializerNames,blsLibWordNames,List.mem_append,
    List.mem_cons,List.not_mem_nil,or_false,not_or] at notWritten
  obtain ⟨⟨a,b,c,d,e⟩,f,g,h,i,j,k,l,m⟩ := notWritten
  simp [blsInitGlobals,blsLibGlobals,fpAccelGlobals,fp2AccelInitGlobals,blsG1AccelInitGlobals,
    HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notHeap,Ne.symm a,Ne.symm b,Ne.symm c,
    Ne.symm d,Ne.symm e,Ne.symm f,Ne.symm g,Ne.symm h,Ne.symm i,Ne.symm j,Ne.symm k,Ne.symm l,Ne.symm m]

theorem firstEightInitializerGlobals_remaining_lookup (globals : HolFiniteMapExact MlS (ValueHOL 64))
    (name : MlS) (member : name ∈ remainingInitializerNames) :
    (firstEightInitializerGlobals globals).lookup name = globals.lookup name := by
  have distinct : ∀ name ∈ remainingInitializerNames,
      name ≠ ofString "heap_ptr" ∧ name ≠ ofString "secp_accel_scratch" ∧
      name ≠ ofString "scratch_ptr" ∧ name ≠ ofString "frame_mem_ptr" ∧
      (∀ entry ∈ sha256InitAllocations, name ≠ entry.1) ∧
      (∀ entry ∈ keccakInitAllocations, name ≠ entry.1) ∧
      (∀ entry ∈ sszInitAllocations, name ≠ entry.1) ∧
      (∀ entry ∈ mptInitAllocations, name ≠ entry.1) ∧
      (∀ entry ∈ u256WorkspaceAllocations, name ≠ entry.1) ∧ name ∉ bn254InitNames := by decide
  obtain ⟨notHeap,notSecp,notScratch,notFrame,notSha,notKeccak,notSsz,notMpt,notWorkspace,notBn⟩ := distinct name member
  rw [firstEightInitializerGlobals,bn254InitGlobals_other _ _ _ notHeap notBn,
    firstSevenInitializerGlobals,secpInitActualGlobals]
  simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notSecp,Ne.symm notHeap]
  rw [firstSixInitializerGlobals,
    globalAllocationGlobals_lookup_other _ _ _ _ notHeap notWorkspace,
    globalAllocationGlobals_lookup_other _ _ _ _ notHeap notMpt]
  exact firstFourInitializerGlobals_lookup_other globals name notHeap notScratch notFrame notSha notKeccak notSsz

/-- Later initialization flags and pointer slots are still their original
main-entry bindings after the first nine stages. -/
theorem firstNineInitializerGlobals_remaining_lookup (globals : HolFiniteMapExact MlS (ValueHOL 64))
    (name : MlS) (member : name ∈ remainingInitializerNames) :
    (firstNineInitializerGlobals globals).lookup name = globals.lookup name := by
  have distinct : ∀ name ∈ remainingInitializerNames,
      name ≠ ofString "heap_ptr" ∧ name ∉ blsInitializerNames := by decide
  obtain ⟨notHeap,notBls⟩ := distinct name member
  rw [firstNineInitializerGlobals,blsInitGlobals_lookup_other _ _ _ notHeap notBls]
  exact firstEightInitializerGlobals_remaining_lookup globals name member

theorem firstNineInitializerGlobals_keccak (globals : HolFiniteMapExact MlS (ValueHOL 64)) :
    (firstNineInitializerGlobals globals).lookup (ofString "keccak_st") = some (.val (.word 2713714976)) ∧
      (firstNineInitializerGlobals globals).lookup (ofString "keccak_pad") = some (.val (.word 2713715176)) := by
  have retained (key : MlS) (notHeap : key ≠ ofString "heap_ptr")
      (notSecp : key ≠ ofString "secp_accel_scratch") (notBn : key ∉ bn254InitNames)
      (notBls : key ∉ blsInitializerNames) :
      (firstNineInitializerGlobals globals).lookup key = (firstSixInitializerGlobals globals).lookup key := by
    rw [firstNineInitializerGlobals,blsInitGlobals_lookup_other _ _ _ notHeap notBls,
      firstEightInitializerGlobals,bn254InitGlobals_other _ _ _ notHeap notBn,
      firstSevenInitializerGlobals,secpInitActualGlobals]
    simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notHeap,Ne.symm notSecp]
  rw [retained _ (by decide) (by decide) (by decide) (by decide),
    retained _ (by decide) (by decide) (by decide) (by decide)]
  obtain ⟨_,_,_,_,state,pad,_⟩ := firstSixInitializerGlobals_layout globals
  exact ⟨state,pad⟩

#print axioms firstNineInitializerGlobals_remaining_lookup
#print axioms firstNineInitializerGlobals_keccak
end InitECandidate.Runtime
