import InitECandidate.Runtime.WitnessDecodeModeSource
import InitECandidate.Runtime.WitnessExtensionStoresProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normal completion of the real completed decode tail changes only result and
mode. The actual run discharges assignment validity, without assumed locals. -/
theorem witness_decode_completed_normal_exact {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (node : BitVec 64)
    (atD : s.locals.lookup (ofString "d") = some (.rStruct [.val (.word (0#64)),.val (.word node)]))
    (run : evaluateHOLFiniteState s witnessDecodeTail = (none,post)) :
    post = setVarHOLFinite (ofString "mode") (.val (.word (0#64)))
        (setVarHOLFinite (ofString "result") (.val (.word node)) s) := by
  have condition : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.rfield 0 (.var .local (ofString "d"))) (.const 0)) = some (.val (.word (1#64))) := by
    simp [evalHOLExact,atD,Compiler.Encoders.Asm.wordCmpHOL]
  rw [source_witness_decode_tail,evaluateHOLFiniteState_ite,condition] at run
  change evaluateHOLFiniteState s witnessDecodeCompleted = (none,post) at run
  rw [source_witness_decode_completed] at run
  obtain ⟨middle,first,last⟩ := witness_extension_sequence_normal_parts s post _ _ run
  obtain ⟨result,evaluated,middleEq⟩ := evaluate_local_assign_normal_value s middle _ _ first
  have resultEq : result = .val (.word node) := by
    simpa [evalHOLExact,atD] using evaluated.symm
  subst result
  obtain ⟨mode,evaluated,postEq⟩ := evaluate_local_assign_normal_value middle post _ _ last
  have modeEq : mode = .val (.word (0#64)) := by simpa [evalHOLExact] using evaluated.symm
  subst mode
  rw [postEq,middleEq]

#print axioms witness_decode_completed_normal_exact
end InitECandidate.Runtime
