import InitECandidate.Runtime.MainFirstSevenInitializers
import InitECandidate.Runtime.Bn254InitActualHeap
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- None of the first seven initializers writes a BN254 global. -/
theorem firstSevenInitializerGlobals_bn254_lookup (globals : HolFiniteMapExact MlS (ValueHOL 64))
    (name : MlS) (member : name ∈ bn254InitNames) :
    (firstSevenInitializerGlobals globals).lookup name = globals.lookup name := by
  have distinct : ∀ name ∈ bn254InitNames,
      name ≠ ofString "heap_ptr" ∧ name ≠ ofString "secp_accel_scratch" ∧
      name ≠ ofString "scratch_ptr" ∧ name ≠ ofString "frame_mem_ptr" ∧
      (∀ entry ∈ sha256InitAllocations, name ≠ entry.1) ∧
      (∀ entry ∈ keccakInitAllocations, name ≠ entry.1) ∧
      (∀ entry ∈ sszInitAllocations, name ≠ entry.1) ∧
      (∀ entry ∈ mptInitAllocations, name ≠ entry.1) ∧
      (∀ entry ∈ u256WorkspaceAllocations, name ≠ entry.1) := by decide
  obtain ⟨notHeap,notSecp,notScratch,notFrame,notSha,notKeccak,notSsz,notMpt,notWorkspace⟩ := distinct name member
  rw [firstSevenInitializerGlobals,secpInitActualGlobals]
  simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notSecp,Ne.symm notHeap]
  rw [firstSixInitializerGlobals,
    globalAllocationGlobals_lookup_other _ _ _ _ notHeap notWorkspace,
    globalAllocationGlobals_lookup_other _ _ _ _ notHeap notMpt]
  exact firstFourInitializerGlobals_lookup_other globals name notHeap notScratch notFrame notSha notKeccak notSsz

#print axioms firstSevenInitializerGlobals_bn254_lookup
end InitECandidate.Runtime
