import InitECandidate.Runtime.AllInitializerHeaderWorkspace
import InitECandidate.Runtime.CanonicalOriginalSourceFields
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
/-- The startup calls retain the world pointer bindings for the later initializer. -/
theorem allInitializerGlobals_world_kept (globals : HolFiniteMapExact MlS (ValueHOL 64)) :
 (allInitializerGlobals globals).lookup (ofString "ws")=globals.lookup (ofString "ws") ∧
 (allInitializerGlobals globals).lookup (ofString "bs")=globals.lookup (ofString "bs") := by
 exact ⟨rfl,rfl⟩
/-- The actual MPT startup allocation installs this concrete empty-root pointer. -/
theorem allInitializerGlobals_empty_root (globals : HolFiniteMapExact MlS (ValueHOL 64)) :
 (allInitializerGlobals globals).lookup (ofString "empty_trie_root")=some (.val (.word 2713717456)) := by
 rfl
/-- The startup MPT output buffer remains available to both database builds. -/
theorem allInitializerGlobals_mpt_hash_scratch (globals : HolFiniteMapExact MlS (ValueHOL 64)) :
 (allInitializerGlobals globals).lookup (ofString "mpt_hash_scratch")=some (.val (.word 2713717584)) := by
 rfl
#print axioms allInitializerGlobals_mpt_hash_scratch
/-- Original declaration initialization supplies actual typed zero world pointers. -/
theorem canonical_original_world_globals (input : Guest.InputBlob) :
 (canonicalOriginalSourceEntry input).globals.lookup (ofString "ws")=some (.val (.word 0)) ∧
 (canonicalOriginalSourceEntry input).globals.lookup (ofString "bs")=some (.val (.word 0)) := by
 rw [canonical_original_source_fields]
 exact ⟨rfl,rfl⟩
#print axioms allInitializerGlobals_world_kept
#print axioms allInitializerGlobals_empty_root
#print axioms canonical_original_world_globals
end InitECandidate.Runtime
