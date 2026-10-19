import InitECandidate.Runtime.WitnessDecodeModeSource
import InitECandidate.Runtime.WitnessExtensionStoresProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

private theorem conditional_bit_assignment_normal {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (name : MlS) (condition : ExpHOL 64)
    (run : evaluateHOLFiniteState s (.ite condition (.assign .local name (.const 1))
      (.assign .local name (.const 0))) = (none,post)) :
    ∃ bit : BitVec 64, (bit = 0 ∨ bit = 1) ∧ post = setVarHOLFinite name (.val (.word bit)) s := by
  rw [evaluateHOLFiniteState_ite] at run
  split at run
  · split at run
    · obtain ⟨value,evaluated,same⟩ := evaluate_local_assign_normal_value s post name (.const 0) run
      have equal : value = .val (.word (0#64)) := by simpa [evalHOLExact] using evaluated.symm
      subst value
      exact ⟨0,Or.inl rfl,same⟩
    · obtain ⟨value,evaluated,same⟩ := evaluate_local_assign_normal_value s post name (.const 1) run
      have equal : value = .val (.word (1#64)) := by simpa [evalHOLExact] using evaluated.symm
      subst value
      exact ⟨1,Or.inr rfl,same⟩
  · cases run

/-- The original pending decode tail links and selects a fresh top record,
chooses slot zero or one and enters resolve mode. Failed stores/loads are
excluded by the actual normal run, rather than assumed readable upfront. -/
theorem witness_decode_push_normal_control {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (record : BitVec 64)
    (atD : s.locals.lookup (ofString "d") = some (.rStruct [.val (.word (1#64)),.val (.word record)]))
    (run : evaluateHOLFiniteState s witnessDecodeTail = (none,post)) :
    post.locals.lookup (ofString "top") = some (.val (.word record)) ∧
      post.locals.lookup (ofString "mode") = some (.val (.word (2#64))) ∧
      ∃ slot : BitVec 64, (slot = 0 ∨ slot = 1) ∧
        post.locals.lookup (ofString "slot") = some (.val (.word slot)) := by
  have condition : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.rfield 0 (.var .local (ofString "d"))) (.const 0)) = some (.val (.word (0#64))) := by
    simp [evalHOLExact,atD,Compiler.Encoders.Asm.wordCmpHOL]
  rw [source_witness_decode_tail,evaluateHOLFiniteState_ite,condition] at run
  change evaluateHOLFiniteState s witnessDecodePush = (none,post) at run
  rw [source_witness_decode_push] at run
  obtain ⟨stored,storeRun,storeLocals,rest⟩ := evaluate_store_sequence_normal s post _ _ _ run
  obtain ⟨selected,selectRun,rest⟩ := witness_extension_sequence_normal_parts stored post _ _ rest
  obtain ⟨value,evaluated,selectedEq⟩ := evaluate_local_assign_normal_value stored selected _ _ selectRun
  have valueEq : value = .val (.word record) := by simpa [evalHOLExact,storeLocals,atD] using evaluated.symm
  subst value
  obtain ⟨slotted,slotRun,modeRun⟩ := witness_extension_sequence_normal_parts selected post _ _ rest
  obtain ⟨slot,slotBit,slottedEq⟩ := conditional_bit_assignment_normal selected slotted (ofString "slot") _ slotRun
  obtain ⟨value,evaluated,postEq⟩ := evaluate_local_assign_normal_value slotted post _ _ modeRun
  have modeEq : value = .val (.word (2#64)) := by simpa [evalHOLExact] using evaluated.symm
  subst value
  rw [postEq,slottedEq,selectedEq]
  refine ⟨?_,?_,slot,slotBit,?_⟩ <;>
    simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms witness_decode_push_normal_control
end InitECandidate.Runtime
