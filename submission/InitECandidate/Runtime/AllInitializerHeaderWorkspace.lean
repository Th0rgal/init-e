import InitECandidate.Runtime.MainAllInitializers
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000

theorem allInitializerGlobals_scratch (globals : HolFiniteMapExact MlS (ValueHOL 64)) :
    (allInitializerGlobals globals).lookup (ofString "scratch_ptr")=some (.val (.word 2713714688)) := by
  rfl
#print axioms allInitializerGlobals_scratch

theorem allInitializerGlobals_frame (globals : HolFiniteMapExact MlS (ValueHOL 64)) :
    (allInitializerGlobals globals).lookup (ofString "frame_mem_ptr")=some (.val (.word 2701135872)) := by
  rfl
#print axioms allInitializerGlobals_frame

theorem allInitializerGlobals_keccak_state (globals : HolFiniteMapExact MlS (ValueHOL 64)) :
    (allInitializerGlobals globals).lookup (ofString "keccak_st")=some (.val (.word 2713714976)) := by
  rfl
#print axioms allInitializerGlobals_keccak_state

theorem allInitializerGlobals_keccak_pad (globals : HolFiniteMapExact MlS (ValueHOL 64)) :
    (allInitializerGlobals globals).lookup (ofString "keccak_pad")=some (.val (.word 2713715176)) := by
  rfl
#print axioms allInitializerGlobals_keccak_pad
end InitECandidate.Runtime
