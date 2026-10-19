import InitECandidate.Runtime.DecodeStepAllocatedRecordMetadata
import InitECandidate.Runtime.DecodeStepPushRecordIdentity
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def DecoderRecordFields {F : Type} (s : PanSemStateFiniteExact 64 F)
    (record array pointer length stage : BitVec 64) : Prop :=
  s.memory (record+8) = .word stage ∧ s.memory (record+24) = .word array ∧
  s.memory (record+48) = .word pointer ∧ s.memory (record+56) = .word length ∧
  (stage=1 → ∃ nibs count : BitVec 64, s.memory (record+64) = .word nibs ∧ s.memory (record+72) = .word count) ∧
  (stage=2 → ∃ branch : BitVec 64, s.memory (record+16) = .word branch ∧
    s.memory (record+32) = .word 0 ∧ s.memory (record+40) = .word 0)

theorem decode_step_extension_suffix_returned_fields {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (scratch frame arr p n nibs count leaf : BitVec 64)
    (at_arr : s.locals.lookup (ofString "arr") = some (.val (.word arr)))
    (at_p : s.locals.lookup (ofString "p") = some (.val (.word p)))
    (at_n : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (at_cn : s.locals.lookup (ofString "cn") = some (.rStruct [.val (.word nibs),.val (.word count),.val (.word leaf)]))
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (ordered : frame ≤ scratch) (code : s.code = originalRuntimeCode) (ticks : 3 ≤ s.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState s decodeStepExtensionSuffix = (some (.returned value),post)) :
    DecoderRecordFields post (scratchAllocationEnd scratch 88) arr p n 1 := by
  rw [source_decodeStep_extension_suffix] at run
  obtain ⟨next,normal,tailRun⟩ := seq_returned_of_nonreturning_first
    (by intro v; exact evaluate_noDirectReturn _ rfl s v) run
  have same := mpt_fail_guard_normal_state s next _ 7 code normal
  subst next
  obtain ⟨stage,array,pointer,length,nibField,countField⟩ := decode_step_extension_record_returned_metadata s post scratch frame arr p n nibs count leaf
    at_arr at_p at_n at_cn scratchGlobal frameGlobal ordered code (by omega) value tailRun
  exact ⟨stage,array,pointer,length,fun _ => ⟨nibs,count,nibField,countField⟩,by intro impossible; cases impossible⟩

theorem decode_step_path_push_returned_fields {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (scratch frame arr p n nibs count leaf record : BitVec 64)
    (at_arr : s.locals.lookup (ofString "arr") = some (.val (.word arr)))
    (at_p : s.locals.lookup (ofString "p") = some (.val (.word p)))
    (at_n : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (at_cn : s.locals.lookup (ofString "cn") = some (.rStruct [.val (.word nibs),.val (.word count),.val (.word leaf)]))
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (ordered : frame ≤ scratch) (code : s.code = originalRuntimeCode) (ticks : 3 ≤ s.clock)
    (run : evaluateHOLFiniteState s decodeStepCompactContinuation =
      (some (.returned (.rStruct [.val (.word (1 : BitVec 64)),.val (.word record)])),post)) :
    DecoderRecordFields post record arr p n 1 := by
  have recordEq := decode_step_path_push_returned_record s post nibs count leaf scratch frame record at_cn
    scratchGlobal frameGlobal code ordered ticks run
  by_cases zero : leaf=0
  · subst leaf
    rw [evaluate_decodeStep_extension_dispatch s nibs count at_cn] at run
    rw [recordEq]
    exact decode_step_extension_suffix_returned_fields s post scratch frame arr p n nibs count 0
      at_arr at_p at_n at_cn scratchGlobal frameGlobal ordered code ticks _ run
  · rw [evaluate_decode_step_leaf_dispatch s nibs count leaf zero at_cn] at run
    obtain ⟨value,shape⟩ := decode_step_leaf_branch_returned_flag s post _ run
    have firstEq := (List.cons.inj (ValueHOL.rStruct.inj shape)).1
    have impossible : (1 : BitVec 64)=0 := HolWordLab.word.inj (ValueHOL.val.inj firstEq)
    exact False.elim ((by decide : (1 : BitVec 64)≠0) impossible)

theorem decode_step_branch_construction_returned_fields {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (scratch frame arr p n : BitVec 64)
    (at_arr : s.locals.lookup (ofString "arr") = some (.val (.word arr)))
    (at_p : s.locals.lookup (ofString "p") = some (.val (.word p)))
    (at_n : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (ordered : frame ≤ scratch) (code : s.code = originalRuntimeCode) (ticks : 43 ≤ s.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState s decodeStepBranchConstruction = (some (.returned value),post)) :
    DecoderRecordFields post (scratchAllocationEnd scratch 88) arr p n 2 := by
  let entry := callEntryStateHOLFinite s (HolFiniteMapExact.empty : HolFiniteMapExact MlS (ValueHOL 64))
  have lookup := pan_no_args_lookup s.code.lookup (ofString "node_new_branch")
    (sourceFunctionBody Guest.guestFn_node_new_branch)
    (by rw [code]; exact originalRuntimeCode_nodeNewBranch_lookup)
  rw [source_decode_step_branch_construction] at run
  obtain ⟨allocated,bodyPost,output,bodyRun,checked,tailRun,postEq⟩ :=
    evaluate_decCall_checked_returned_exact_scope s post (ofString "br") (ofString "node_new_branch") .one .one [] []
      (sourceFunctionBody Guest.guestFn_node_new_branch) decodeStepBranchRecord HolFiniteMapExact.empty value rfl lookup run
  obtain ⟨br,rfl⟩ := value_word_of_shape_one allocated ((shapeEqHOL_eq_true _ _).mp checked.1)
  have bound := runBounded_node_new_branch_body entry code (by change 40 ≤ s.clock-1; omega)
  unfold RunBounded at bound
  rw [bodyRun] at bound
  have scratchKept := node_new_branch_workspace_frame entry code (ofString "scratch_ptr") (by simp [nodeConstructorWorkspace])
  have frameKept := node_new_branch_workspace_frame entry code (ofString "frame_mem_ptr") (by simp [nodeConstructorWorkspace])
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_node_new_branch)
  rw [bodyRun] at scratchKept frameKept metadata
  let ready := setVarHOLFinite (ofString "br") (.val (.word br)) {bodyPost with locals := s.locals}
  have other : ∀ name, name ≠ ofString "br" → ready.locals.lookup name = s.locals.lookup name := by
    intro name different
    simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  obtain ⟨stage,branchField,array,index,occupied,pointer,length⟩ := decode_step_branch_record_returned_metadata ready output
    scratch frame arr p n br ((other _ (by decide)).trans at_arr) ((other _ (by decide)).trans at_p)
    ((other _ (by decide)).trans at_n) (by simp [ready,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (scratchKept.trans scratchGlobal) (frameKept.trans frameGlobal) ordered (metadata.1.trans code)
    (by change 2 ≤ bodyPost.clock; have spent := bound.1; change s.clock-1 ≤ bodyPost.clock+40 at spent; omega)
    value tailRun
  rw [postEq]
  exact ⟨stage,array,pointer,length,(by intro impossible; cases impossible),fun _ => ⟨br,branchField,index,occupied⟩⟩

#print axioms decode_step_extension_suffix_returned_fields
#print axioms decode_step_path_push_returned_fields
#print axioms decode_step_branch_construction_returned_fields
end InitECandidate.Runtime
