import InitECandidate.Runtime.MptInitSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem mptInit_allocation_globals (globals : HolFiniteMapExact MlS (ValueHOL 64)) :
    let allocated := globalAllocationGlobals globals 2713717456 mptInitAllocations
    allocated.lookup (ofString "mpt_hash_scratch") = some (.val (.word 2713717584)) ∧
      allocated.lookup (ofString "empty_trie_root") = some (.val (.word 2713717456)) ∧
      allocated.lookup (ofString "empty_code_hash") = some (.val (.word 2713717488)) ∧
      allocated.lookup (ofString "heap_ptr") = some (.val (.word 2713717640)) := by
  simp [globalAllocationGlobals,mptInitAllocations,HolFiniteMapExact.lookup_update,FUPDATE,ofString]
  decide

#print axioms mptInit_allocation_globals
end InitECandidate.Runtime
