import InitECandidate.Runtime.DecodeStepCompactCall
import InitECandidate.Runtime.CompactNibbleUniformBodyBound
import InitECandidate.Runtime.BoundedDecCallReach
import InitECandidate.Runtime.NodeDecoderWorkspaceFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def compactNibbleCallee (pointer length : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  (HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))).update (ofString "n",.val (.word length))

/-- The actual trie-parser compact call reaches its real continuation with the
same bounded callee execution and checked three-word result, without assuming
allocation or byte accesses succeed. -/
theorem decode_step_compact_reaches {F : Type} (s : PanSemStateFiniteExact 64 F)
    (kind pointer length consumed : BitVec 64) (small : length.toNat + 4 < 2^64)
    (atItem : s.locals.lookup (ofString "pi") = some
      (.rStruct [.val (.word kind),.val (.word pointer),.val (.word length),.val (.word consumed)]))
    (code : s.code = originalRuntimeCode) (budget : length.toNat / 4 + 7 ≤ s.clock) :
    Reaches s decodeStepCompactCall
      (fun next => ∃ value post,
        evaluateHOLFiniteState (callEntryStateHOLFinite s (compactNibbleCallee pointer length))
          (sourceFunctionBody Guest.guestFn_compact_to_nibbles) = (some (.returned value),post) ∧
        shapeEqHOL (shapeOfHOLExact value) (.comb [.one,.one,.one]) = true ∧
        next = setVarHOLFinite (ofString "cn") value {post with locals := s.locals} ∧
        next.code = s.code ∧ next.memaddrs = s.memaddrs ∧
        next.globals.lookup (ofString "scratch_ptr") = s.globals.lookup (ofString "scratch_ptr") ∧
        next.globals.lookup (ofString "frame_mem_ptr") = s.globals.lookup (ofString "frame_mem_ptr"))
      (length.toNat / 4 + 7) decodeStepCompactContinuation := by
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
  rw [source_decodeStep_compact_call]
  apply bounded_decCall_reaches s (ofString "cn") (ofString "compact_to_nibbles") (.comb [.one,.one,.one])
    (.comb [.one,.one,.one]) _ _ _ _ (compactNibbleCallee pointer length) (length.toNat / 4 + 6) _
    args lookup (by omega) bounded
  intro value post run shapes
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_compact_to_nibbles)
  rw [run] at metadata
  have scratchKept := compact_nibble_workspace_frame entry code (ofString "scratch_ptr") (by simp [nodeDecoderWorkspace])
  have frameKept := compact_nibble_workspace_frame entry code (ofString "frame_mem_ptr") (by simp [nodeDecoderWorkspace])
  rw [run] at scratchKept frameKept
  exact ⟨value,post,run,shapes.1,rfl,metadata.1,metadata.2.1,scratchKept,frameKept⟩

#print axioms decode_step_compact_reaches
end InitECandidate.Runtime
