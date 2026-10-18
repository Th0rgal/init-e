import InitECandidate.Runtime.MainFirstEightInitializers
import InitECandidate.Runtime.BlsPrecompilesInitSuccess
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def blsInitializerNames : List MlS :=
  [ofString "bls_discount",ofString "bls_c",ofString "fp_accel_params",
    ofString "fp2_accel_params",ofString "bls_g1_accel_params"] ++ blsLibWordNames

/-- The preceding eight initializers retain every BLS initialization flag
and pointer slot from the actual main-entry globals. -/
theorem firstEightInitializerGlobals_bls_lookup (globals : HolFiniteMapExact MlS (ValueHOL 64))
    (name : MlS) (member : name ∈ blsInitializerNames) :
    (firstEightInitializerGlobals globals).lookup name = globals.lookup name := by
  have distinct : ∀ name ∈ blsInitializerNames,
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

#print axioms firstEightInitializerGlobals_bls_lookup
end InitECandidate.Runtime
