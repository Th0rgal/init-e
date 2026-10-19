import InitECandidate.Runtime.WitnessResolveModeSource
import InitECandidate.Runtime.WitnessExtensionStoresProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A real resolver hit schedules decoding of exactly its returned slice. It
retains the physical stack top and workspace globals; it does not claim that
hash resolution shrinks the current input slice. -/
theorem witness_resolve_hit_tail_normal_control {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (pointer length hash : BitVec 64)
    (atR : s.locals.lookup (ofString "r") = some
      (.rStruct [.val (.word (1#64)),.val (.word pointer),.val (.word length),.val (.word hash)]))
    (code : s.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState s witnessResolveTail = (none,post)) :
    post.locals.lookup (ofString "cur_p") = some (.val (.word pointer)) ∧
      post.locals.lookup (ofString "cur_n") = some (.val (.word length)) ∧
      post.locals.lookup (ofString "mode") = some (.val (.word (1#64))) ∧
      post.locals.lookup (ofString "top") = s.locals.lookup (ofString "top") ∧
      post.globals = s.globals := by
  have globals := witness_resolve_tail_globals_frame s code
  rw [run] at globals
  have condition : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0)) = some (.val (.word (0#64))) := by
    simp [evalHOLExact,atR,Compiler.Encoders.Asm.wordCmpHOL]
  rw [source_witness_resolve_tail,evaluateHOLFiniteState_ite,condition] at run
  obtain ⟨stored,_,storeLocals,rest⟩ := evaluate_store_sequence_normal s post _ _ _ run
  obtain ⟨pointed,pointerRun,rest⟩ := witness_extension_sequence_normal_parts stored post _ _ rest
  obtain ⟨value,evaluated,pointedEq⟩ := evaluate_local_assign_normal_value stored pointed _ _ pointerRun
  have valueEq : value = .val (.word pointer) := by simpa [evalHOLExact,storeLocals,atR] using evaluated.symm
  subst value
  obtain ⟨sized,lengthRun,modeRun⟩ := witness_extension_sequence_normal_parts pointed post _ _ rest
  obtain ⟨value,evaluated,sizedEq⟩ := evaluate_local_assign_normal_value pointed sized _ _ lengthRun
  have valueEq : value = .val (.word length) := by
    simpa (config := {decide := true}) [evalHOLExact,pointedEq,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      storeLocals,atR] using evaluated.symm
  subst value
  obtain ⟨value,evaluated,postEq⟩ := evaluate_local_assign_normal_value sized post _ _ modeRun
  have valueEq : value = .val (.word (1#64)) := by simpa [evalHOLExact] using evaluated.symm
  subst value
  refine ⟨?_,?_,?_,?_,globals⟩ <;>
    simp (config := {decide := true}) [postEq,sizedEq,pointedEq,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,storeLocals]

/-- A real resolver miss delivers its returned constructed/empty node without
changing the active stack top or workspace globals. -/
theorem witness_resolve_completed_tail_normal_control {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (node unused hash : BitVec 64)
    (atR : s.locals.lookup (ofString "r") = some
      (.rStruct [.val (.word (0#64)),.val (.word node),.val (.word unused),.val (.word hash)]))
    (code : s.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState s witnessResolveTail = (none,post)) :
    post.locals.lookup (ofString "result") = some (.val (.word node)) ∧
      post.locals.lookup (ofString "mode") = some (.val (.word (0#64))) ∧
      post.locals.lookup (ofString "top") = s.locals.lookup (ofString "top") ∧
      post.globals = s.globals := by
  have globals := witness_resolve_tail_globals_frame s code
  rw [run] at globals
  have condition : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.rfield 0 (.var .local (ofString "r"))) (.const 0)) = some (.val (.word (1#64))) := by
    simp [evalHOLExact,atR,Compiler.Encoders.Asm.wordCmpHOL]
  rw [source_witness_resolve_tail,evaluateHOLFiniteState_ite,condition] at run
  obtain ⟨stored,_,storeLocals,rest⟩ := evaluate_store_sequence_normal s post _ _ _ run
  obtain ⟨delivered,resultRun,modeRun⟩ := witness_extension_sequence_normal_parts stored post _ _ rest
  obtain ⟨value,evaluated,deliveredEq⟩ := evaluate_local_assign_normal_value stored delivered _ _ resultRun
  have valueEq : value = .val (.word node) := by simpa [evalHOLExact,storeLocals,atR] using evaluated.symm
  subst value
  obtain ⟨value,evaluated,postEq⟩ := evaluate_local_assign_normal_value delivered post _ _ modeRun
  have valueEq : value = .val (.word (0#64)) := by simpa [evalHOLExact] using evaluated.symm
  subst value
  refine ⟨?_,?_,?_,globals⟩ <;>
    simp (config := {decide := true}) [postEq,deliveredEq,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,storeLocals]

#print axioms witness_resolve_hit_tail_normal_control
#print axioms witness_resolve_completed_tail_normal_control
end InitECandidate.Runtime
