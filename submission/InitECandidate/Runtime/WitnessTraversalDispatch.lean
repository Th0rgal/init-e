import InitECandidate.Runtime.DecodeWitnessNodeLoopSource
import InitECandidate.Runtime.WitnessUnwindModeBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem witness_iteration_dispatch_unwind {F : Type} (s : PanSemStateFiniteExact 64 F)
    (atMode : s.locals.lookup (ofString "mode")=some (.val (.word (0#64)))) :
    evaluateHOLFiniteState s decodeWitnessNodeIteration=evaluateHOLFiniteState s decodeWitnessNodeUnwindMode := by
  rw [source_decode_witness_node_modes]
  simp [evaluateHOLFiniteState_ite,evalHOLExact,atMode,Compiler.Encoders.Asm.wordCmpHOL]
#print axioms witness_iteration_dispatch_unwind

theorem witness_iteration_dispatch_decode {F : Type} (s : PanSemStateFiniteExact 64 F)
    (atMode : s.locals.lookup (ofString "mode")=some (.val (.word (1#64)))) :
    evaluateHOLFiniteState s decodeWitnessNodeIteration=evaluateHOLFiniteState s decodeWitnessNodeDecodeMode := by
  rw [source_decode_witness_node_modes]
  simp [evaluateHOLFiniteState_ite,evalHOLExact,atMode,Compiler.Encoders.Asm.wordCmpHOL]
#print axioms witness_iteration_dispatch_decode

theorem witness_iteration_dispatch_resolve {F : Type} (s : PanSemStateFiniteExact 64 F)
    (atMode : s.locals.lookup (ofString "mode")=some (.val (.word (2#64)))) :
    evaluateHOLFiniteState s decodeWitnessNodeIteration=evaluateHOLFiniteState s decodeWitnessNodeResolveMode := by
  rw [source_decode_witness_node_modes]
  simp [evaluateHOLFiniteState_ite,evalHOLExact,atMode,Compiler.Encoders.Asm.wordCmpHOL]
#print axioms witness_iteration_dispatch_resolve
end InitECandidate.Runtime
