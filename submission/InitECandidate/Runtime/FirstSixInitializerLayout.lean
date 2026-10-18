import InitECandidate.Runtime.MainFirstSixInitializers
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem firstSixInitializerGlobals_layout (globals : HolFiniteMapExact MlS (ValueHOL 64)) :
    let ready := firstSixInitializerGlobals globals
    ready.lookup (ofString "heap_ptr") = some (.val (.word 2713718280)) ∧
      ready.lookup (ofString "scratch_ptr") = some (.val (.word 2713714688)) ∧
      ready.lookup (ofString "frame_mem_ptr") = some (.val (.word 2701135872)) ∧
      ready.lookup (ofString "ssz_offs") = some (.val (.word 2713715344)) ∧
      ready.lookup (ofString "keccak_st") = some (.val (.word 2713714976)) ∧
      ready.lookup (ofString "keccak_pad") = some (.val (.word 2713715176)) ∧
      ready.lookup (ofString "u256_ws") = some (.val (.word 2713717640)) := by
  simp [firstSixInitializerGlobals,firstFourInitializerGlobals,globalAllocationGlobals,
    sha256InitAllocations,keccakInitAllocations,sszInitAllocations,mptInitAllocations,u256WorkspaceAllocations,
    HolFiniteMapExact.lookup_update,FUPDATE,ofString]
  decide

theorem firstSixInitializerGlobals_secp_scratch (globals : HolFiniteMapExact MlS (ValueHOL 64)) :
    (firstSixInitializerGlobals globals).lookup (ofString "secp_accel_scratch") = globals.lookup (ofString "secp_accel_scratch") := by
  rw [firstSixInitializerGlobals,
    globalAllocationGlobals_lookup_other _ _ _ _ (by decide) (by decide),
    globalAllocationGlobals_lookup_other _ _ _ _ (by decide) (by decide)]
  exact firstFourInitializerGlobals_lookup_other globals (ofString "secp_accel_scratch")
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem firstSixInitializerContinuation_secp_zero {F : Type} (state next : PanSemStateFiniteExact 64 F)
    (valid : FirstSixInitializerContinuation state next)
    (zero : state.globals.lookup (ofString "secp_accel_scratch") = some (.val (.word 0))) :
    next.globals.lookup (ofString "secp_accel_scratch") = some (.val (.word 0)) := by
  rw [valid.1,firstSixInitializerGlobals_secp_scratch]
  exact zero

#print axioms firstSixInitializerGlobals_layout
#print axioms firstSixInitializerGlobals_secp_scratch
#print axioms firstSixInitializerContinuation_secp_zero
end InitECandidate.Runtime
