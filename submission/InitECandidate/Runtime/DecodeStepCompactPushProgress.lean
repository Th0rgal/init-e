import InitECandidate.Runtime.DecodeStepCompactReach
import InitECandidate.Runtime.DecodeStepPathPushProgress
import InitECandidate.Runtime.ThreeWordValueShape
import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A push returned through the actual compact decoder call consumes a real
scratch record. The callee's own bounded execution supplies the remaining clock
and its checked returned triple, in the same caller continuation state. -/
theorem decode_step_compact_call_push_returned_progress {F : Type}
    (s post : PanSemStateFiniteExact 64 F)
    (kind pointer length consumed scratch frame record : BitVec 64)
    (small : length.toNat + 4 < 2^64)
    (atItem : s.locals.lookup (ofString "pi") = some
      (.rStruct [.val (.word kind),.val (.word pointer),.val (.word length),.val (.word consumed)]))
    (scratchGlobal : s.globals.lookup (ofString "scratch_ptr") = some (.val (.word scratch)))
    (frameGlobal : s.globals.lookup (ofString "frame_mem_ptr") = some (.val (.word frame)))
    (code : s.code = originalRuntimeCode) (ordered : frame ≤ scratch)
    (budget : length.toNat / 4 + 10 ≤ s.clock)
    (run : evaluateHOLFiniteState s decodeStepCompactCall =
      (some (.returned (.rStruct [.val (.word (1 : BitVec 64)),.val (.word record)])),post)) :
    post.globals.lookup (ofString "scratch_ptr") = some (.val (.word (scratchAllocationEnd scratch 88))) ∧
      frame.toNat ≤ (scratchAllocationEnd scratch 88).toNat ∧
      (scratchAllocationEnd scratch 88).toNat + 88 ≤ scratch.toNat := by
  let entry := callEntryStateHOLFinite s (compactNibbleCallee pointer length)
  have p : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp (config := {decide := true}) [entry,compactNibbleCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have n : entry.locals.lookup (ofString "n") = some (.val (.word length)) := by
    simp [entry,compactNibbleCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have args : evalListHOLFinite s (h := fun a => Classical.propDecidable (s.memaddrs a))
      [.rfield 1 (.var .local (ofString "pi")),.rfield 2 (.var .local (ofString "pi"))] =
      some [.val (.word pointer),.val (.word length)] := by
    rw [evalListHOLFinite_eq_toExact]
    simp [evalListHOLExact,evalHOLExact,atItem]
  have lookup := pan_two_word_lookup_shape s.code.lookup (ofString "compact_to_nibbles")
    (ofString "p") (ofString "n") (sourceFunctionBody Guest.guestFn_compact_to_nibbles)
    (.comb [.one,.one,.one]) pointer length (by decide)
    (by rw [code]; exact originalRuntimeCode_compactNibble_lookup)
  have bounded := runBounded_compact_nibble_body entry pointer length small p n code
    (by change length.toNat / 4 + 6 ≤ s.clock - 1; omega)
  rw [source_decodeStep_compact_call] at run
  obtain ⟨decoded,bodyPost,output,bodyRun,shapes,tailRun,postEq⟩ :=
    evaluate_decCall_checked_returned_exact_scope s post (ofString "cn") (ofString "compact_to_nibbles")
      (.comb [.one,.one,.one]) (.comb [.one,.one,.one]) _ _
      (sourceFunctionBody Guest.guestFn_compact_to_nibbles) decodeStepCompactContinuation
      (compactNibbleCallee pointer length) _ args lookup run
  obtain ⟨nibs,count,leaf,rfl⟩ := value_three_words_of_checked_shape decoded shapes.1
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_compact_to_nibbles)
  have scratchKept := compact_nibble_workspace_frame entry code (ofString "scratch_ptr") (by simp [nodeDecoderWorkspace])
  have frameKept := compact_nibble_workspace_frame entry code (ofString "frame_mem_ptr") (by simp [nodeDecoderWorkspace])
  rw [bodyRun] at metadata scratchKept frameKept
  unfold RunBounded at bounded
  rw [bodyRun] at bounded
  have ticks : 3 ≤ bodyPost.clock := by
    have spent := bounded.1
    change s.clock - 1 ≤ bodyPost.clock + (length.toNat / 4 + 6) at spent
    omega
  have result := decode_step_path_push_returned_progress
    (setVarHOLFinite (ofString "cn") (.rStruct [.val (.word nibs),.val (.word count),.val (.word leaf)])
      {bodyPost with locals := s.locals}) output nibs count leaf scratch frame record
    (by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (scratchKept.trans scratchGlobal) (frameKept.trans frameGlobal) (metadata.1.trans code) ordered ticks tailRun
  rw [postEq]
  exact result

#print axioms decode_step_compact_call_push_returned_progress
end InitECandidate.Runtime
