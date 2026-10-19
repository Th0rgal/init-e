import InitECandidate.Runtime.DecodeStepRecordMetadata
import InitECandidate.Runtime.ScratchParserReturnedEnvironment
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem decode_step_extension_record_returned_metadata {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (scratch frame arr p n nibs count leaf : BitVec 64)
    (at_arr : s.locals.lookup (ofString "arr") = some (.val (.word arr)))
    (at_p : s.locals.lookup (ofString "p") = some (.val (.word p)))
    (at_n : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (at_cn : s.locals.lookup (ofString "cn") = some (.rStruct [.val (.word nibs),.val (.word count),.val (.word leaf)]))
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (ordered : frame ≤ scratch) (code : s.code = originalRuntimeCode) (ticks : 2 ≤ s.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState s decodeStepExtensionRecord = (some (.returned value),post)) :
    post.memory (scratchAllocationEnd scratch 88+8) = .word 1 ∧
    post.memory (scratchAllocationEnd scratch 88+24) = .word arr ∧
    post.memory (scratchAllocationEnd scratch 88+48) = .word p ∧
    post.memory (scratchAllocationEnd scratch 88+56) = .word n ∧
    post.memory (scratchAllocationEnd scratch 88+64) = .word nibs ∧
    post.memory (scratchAllocationEnd scratch 88+72) = .word count := by
  rw [source_decodeStep_extension_record] at run
  obtain ⟨ready,output,locals,memory,heap,readyCode,tailRun,postMemory,postGlobals,recordBefore⟩ :=
    scratch_parser_declaration_returned_environment s post scratch frame (ofString "rec") decodeStepExtensionStores value
      scratchGlobal frameGlobal ordered code ticks run
  have atRecord : ready.locals.lookup (ofString "rec") = some (.val (.word (scratchAllocationEnd scratch 88))) := by
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have other : ∀ name, name ≠ ofString "rec" → ready.locals.lookup name = s.locals.lookup name := by
    intro name different
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have fields := decode_step_extension_stores_returned_metadata ready output (scratchAllocationEnd scratch 88)
    arr p n nibs count leaf atRecord ((other _ (by decide)).trans at_arr) ((other _ (by decide)).trans at_p) ((other _ (by decide)).trans at_n) ((other _ (by decide)).trans at_cn) value tailRun
  rw [postMemory]
  exact fields

#print axioms decode_step_extension_record_returned_metadata

theorem decode_step_branch_record_returned_metadata {F : Type}
    (s post : PanSemStateFiniteExact 64 F) (scratch frame arr p n br : BitVec 64)
    (at_arr : s.locals.lookup (ofString "arr") = some (.val (.word arr)))
    (at_p : s.locals.lookup (ofString "p") = some (.val (.word p)))
    (at_n : s.locals.lookup (ofString "n") = some (.val (.word n)))
    (at_br : s.locals.lookup (ofString "br") = some (.val (.word br)))
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (ordered : frame ≤ scratch) (code : s.code = originalRuntimeCode) (ticks : 2 ≤ s.clock)
    (value : ValueHOL 64) (run : evaluateHOLFiniteState s decodeStepBranchRecord = (some (.returned value),post)) :
    post.memory (scratchAllocationEnd scratch 88+8) = .word 2 ∧
    post.memory (scratchAllocationEnd scratch 88+16) = .word br ∧
    post.memory (scratchAllocationEnd scratch 88+24) = .word arr ∧
    post.memory (scratchAllocationEnd scratch 88+32) = .word 0 ∧
    post.memory (scratchAllocationEnd scratch 88+40) = .word 0 ∧
    post.memory (scratchAllocationEnd scratch 88+48) = .word p ∧
    post.memory (scratchAllocationEnd scratch 88+56) = .word n := by
  rw [source_decode_step_branch_record] at run
  obtain ⟨ready,output,locals,memory,heap,readyCode,tailRun,postMemory,postGlobals,recordBefore⟩ :=
    scratch_parser_declaration_returned_environment s post scratch frame (ofString "rec2") decodeStepBranchStores value
      scratchGlobal frameGlobal ordered code ticks run
  have atRecord : ready.locals.lookup (ofString "rec2") = some (.val (.word (scratchAllocationEnd scratch 88))) := by
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE]
  have other : ∀ name, name ≠ ofString "rec2" → ready.locals.lookup name = s.locals.lookup name := by
    intro name different
    rw [locals]; simp [HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different]
  have fields := decode_step_branch_stores_returned_metadata ready output (scratchAllocationEnd scratch 88)
    arr p n br atRecord ((other _ (by decide)).trans at_arr) ((other _ (by decide)).trans at_p) ((other _ (by decide)).trans at_n) ((other _ (by decide)).trans at_br) value tailRun
  rw [postMemory]
  exact fields

#print axioms decode_step_branch_record_returned_metadata
end InitECandidate.Runtime
