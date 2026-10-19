import InitECandidate.Runtime.WitnessSelectedSlot
import InitECandidate.Runtime.WitnessDecodePushProgress
import InitECandidate.Runtime.WitnessDecodePushLink
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-- The actual pending tail selects slot from its real final record stage.
Final metadata may be supplied by the separately checked actual decoder. -/
theorem witness_decode_push_normal_stage_slot {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (record stage : BitVec 64)
    (atD : s.locals.lookup (ofString "d")=some (.rStruct [.val (.word (1#64)),.val (.word record)]))
    (stageReadable : post.memaddrs (record+8)) (stageCell : post.memory (record+8)=.word stage)
    (run : evaluateHOLFiniteState s witnessDecodeTail=(none,post)) :
    post.locals.lookup (ofString "top")=some (.val (.word record)) ∧
    post.locals.lookup (ofString "slot")=some (.val (.word (if stage=1 then 1 else 0))) := by
  have condition : @evalHOLExact 64 F _ s.toExact (fun a => Classical.propDecidable (s.memaddrs a))
      (.cmp .equal (.rfield 0 (.var .local (ofString "d"))) (.const 0))=some (.val (.word (0#64))) := by
    simp [evalHOLExact,atD,Compiler.Encoders.Asm.wordCmpHOL]
  rw [source_witness_decode_tail,evaluateHOLFiniteState_ite,condition] at run
  change evaluateHOLFiniteState s witnessDecodePush=(none,post) at run
  rw [source_witness_decode_push] at run
  obtain ⟨stored,storeRun,storeLocals,rest⟩ := evaluate_store_sequence_normal s post _ _ _ run
  obtain ⟨selected,selectRun,rest⟩ := witness_extension_sequence_normal_parts stored post _ _ rest
  obtain ⟨value,evaluated,selectedEq⟩ := evaluate_local_assign_normal_value stored selected _ _ selectRun
  have valueEq : value=.val (.word record) := by simpa [evalHOLExact,storeLocals,atD] using evaluated.symm
  subst value
  have selectedTop : selected.locals.lookup (ofString "top")=some (.val (.word record)) := by
    simp [selectedEq,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  let suffix : ProgHOL 64 := .seq
    (.ite (.cmp .equal (.load .one (.op .add [.var .local (ofString "top"),.const 8])) (.const 1))
      (.assign .local (ofString "slot") (.const 1)) (.assign .local (ofString "slot") (.const 0)))
    (.assign .local (ofString "mode") (.const 2))
  change evaluateHOLFiniteState selected suffix=(none,post) at rest
  have memory := evaluate_readOnly_memory suffix (by rfl) selected
  have metadata := evaluateHOLFiniteState_metadata selected suffix
  rw [rest] at memory metadata
  have conditionStage : @evalHOLExact 64 F _ selected.toExact (fun a => Classical.propDecidable (selected.memaddrs a))
      (.cmp .equal (.load .one (.op .add [.var .local (ofString "top"),.const 8])) (.const 1))=
      some (.val (.word (if stage=1 then 1 else 0))) := by
    have accessible : selected.memaddrs (record+8#64) := by rw [←metadata.2.1];exact stageReadable
    have cell : selected.memory (record+8#64)=.word stage := by rw [←memory];exact stageCell
    simp [evalHOLExact,evalListHOLExact,selectedTop,wordOpHOL,wordOp,valueIsWord,valueWord,isWfShapeExactHOL,
      memLoadHOLExact,accessible,cell,Compiler.Encoders.Asm.wordCmpHOL]
  obtain ⟨slotted,slotRun,modeRun⟩ := witness_extension_sequence_normal_parts selected post _ _ rest
  have slottedEq : slotted=setVarHOLFinite (ofString "slot") (.val (.word (if stage=1 then 1 else 0))) selected := by
    rw [evaluateHOLFiniteState_ite,conditionStage] at slotRun
    by_cases one : stage=1
    · simp only [if_pos one] at slotRun ⊢
      change evaluateHOLFiniteState selected (.assign .local (ofString "slot") (.const 1))=(none,slotted) at slotRun
      obtain ⟨v,ev,eq⟩ := evaluate_local_assign_normal_value selected slotted _ _ slotRun
      have veq : v=.val (.word (1#64)) := by simpa [evalHOLExact] using ev.symm
      simpa [veq] using eq
    · simp only [if_neg one] at slotRun ⊢
      change evaluateHOLFiniteState selected (.assign .local (ofString "slot") (.const 0))=(none,slotted) at slotRun
      obtain ⟨v,ev,eq⟩ := evaluate_local_assign_normal_value selected slotted _ _ slotRun
      have veq : v=.val (.word (0#64)) := by simpa [evalHOLExact] using ev.symm
      simpa [veq] using eq
  obtain ⟨value,evaluated,postEq⟩ := evaluate_local_assign_normal_value slotted post _ _ modeRun
  rw [postEq,slottedEq]
  constructor
  · simpa (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using selectedTop
  · simp (config := {decide := true}) [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

/-- Fresh actual decoder fields have branch index zero. The actual tail's
stage-driven slot assignment establishes the mode2 selector invariant. -/
theorem witness_decode_push_normal_selected_slot {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (record array pointer length stage : BitVec 64)
    (atD : s.locals.lookup (ofString "d")=some (.rStruct [.val (.word (1#64)),.val (.word record)]))
    (kind : stage=1 ∨ stage=2) (stageReadable : post.memaddrs (record+8))
    (fields : DecoderRecordFields post record array pointer length stage)
    (run : evaluateHOLFiniteState s witnessDecodeTail=(none,post)) :
    WitnessSelectedSlot post record := by
  have slot := (witness_decode_push_normal_stage_slot s post record stage atD stageReadable fields.1 run).2
  rcases kind with one | two
  · subst stage
    exact Or.inl ⟨fields.1,by simpa using slot⟩
  · subst stage
    obtain ⟨branch,atBranch,index,_⟩ := fields.2.2.2.2.2 rfl
    exact Or.inr ⟨fields.1,0,index,by simpa using slot,by decide⟩
#print axioms witness_decode_push_normal_stage_slot
#print axioms witness_decode_push_normal_selected_slot
end InitECandidate.Runtime
