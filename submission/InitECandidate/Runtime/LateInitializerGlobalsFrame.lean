import InitECandidate.Runtime.MainRipemdBlakeInitializers
import InitECandidate.Runtime.MainHeaderEvmForkInitializers
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def lateInitializerNames : List MlS :=
  [ofString "hdr_zero8",ofString "keccak_st",ofString "keccak_pad"] ++
    evmInitAllocations.map Prod.fst ++ forkInitAllocations.map Prod.fst

theorem blake2InitGlobals_lookup_other (globals : HolFiniteMapExact MlS (ValueHOL 64))
    (pointer : BitVec 64) (key : MlS) (notHeap : key ≠ ofString "heap_ptr")
    (notWritten : key ∉ blakeInitializerNames) :
    (blake2InitGlobals globals pointer).lookup key = globals.lookup key := by
  simp only [blakeInitializerNames,List.mem_cons,List.not_mem_nil,or_false,not_or] at notWritten
  obtain ⟨a,b,c,d,e⟩ := notWritten
  simp [blake2InitGlobals,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm notHeap,
    Ne.symm a,Ne.symm b,Ne.symm c,Ne.symm d,Ne.symm e]

/-- RIPEMD and BLAKE2 preserve every binding needed by the last three
initializers, including the already installed Keccak state and padding. -/
theorem ripemdBlakeInitializerGlobals_late_lookup (globals : HolFiniteMapExact MlS (ValueHOL 64))
    (key : MlS) (member : key ∈ lateInitializerNames) :
    (ripemdBlakeInitializerGlobals globals).lookup key = globals.lookup key := by
  have distinct : ∀ key ∈ lateInitializerNames, key ≠ ofString "heap_ptr" ∧
      key ∉ blakeInitializerNames ∧ (∀ entry ∈ ripemdInitAllocations, key ≠ entry.1) := by decide
  obtain ⟨notHeap,notBlake,notRmd⟩ := distinct key member
  rw [ripemdBlakeInitializerGlobals,blake2InitGlobals_lookup_other _ _ _ notHeap notBlake,
    globalAllocationGlobals_lookup_other _ _ _ _ notHeap notRmd]

#print axioms blake2InitGlobals_lookup_other
#print axioms ripemdBlakeInitializerGlobals_late_lookup
end InitECandidate.Runtime
