import InitECandidate.Runtime.HtrPayloadTxBlockBound
import InitECandidate.Runtime.HeapReleaseReturned
import InitECandidate.Runtime.DiscardCallSuccessLocals
import InitECandidate.Runtime.HtabDelBound
import InitECandidate.Runtime.HtrHeapGlobals
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The grouped original block preserves every caller local except the cursor. -/
theorem htrPayload_tx_block_local_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (key : MlS) (different : key ≠ ofString "i")
    (run : evaluateHOLFiniteState state htrPayloadTxBlock = (none,post)) :
    post.locals.lookup key = state.locals.lookup key := by
  have supported : avoidsLocal key htrPayloadTxBlock = true := by
    simp [htrPayloadTxBlock,htrPayloadTxHashCall,htrPayloadTxRelease,htrPayloadTxStep,avoidsLocal,Ne.symm different]
  have frame := evaluate_avoidsLocal_flowing key _ supported state (by rw [run]; exact Or.inl rfl)
  simpa only [run] using frame

/-- Actual normal completion restores the caller's saved heap frontier.
The claim does not assume successful intermediate allocation or readable inputs. -/
theorem htrPayload_tx_block_normal_heap {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (mark : BitVec 64)
    (marker : state.locals.lookup (ofString "m2") = some (.val (.word mark)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state htrPayloadTxBlock = (none,post)) :
    post.globals.lookup (ofString "heap_ptr") = some (.val (.word mark)) := by
  obtain ⟨middle,loop,tail⟩ := seq_normal_parts (by exact run)
  obtain ⟨hashed,hash,release⟩ := seq_normal_parts tail
  have atMiddle := (htrPayload_tx_loop_local_frame state middle (ofString "m2") (by decide) loop).trans marker
  have locals := evaluate_discard_call_success_locals middle (ofString "htr_plist_chunks")
    htrPayloadTxHashArguments (by change (evaluateHOLFiniteState middle htrPayloadTxHashCall).1 = none; rw [hash])
  change (evaluateHOLFiniteState middle htrPayloadTxHashCall).2.locals = middle.locals at locals
  rw [hash] at locals
  have atHashed : hashed.locals.lookup (ofString "m2") = some (.val (.word mark)) := by
    rw [locals]
    exact atMiddle
  have firstCode := evaluateHOLFiniteState_metadata state (.while htrPayloadTxCondition htrPayloadTxStep)
  rw [loop] at firstCode
  have secondCode := evaluateHOLFiniteState_metadata middle htrPayloadTxHashCall
  rw [hash] at secondCode
  exact heapRelease_call_normal hashed post (.var .local (ofString "m2")) mark
    (secondCode.1.trans (firstCode.1.trans code))
    (by simp [evalListHOLExact,evalHOLExact,atHashed]) release

theorem htrPayload_tx_block_heapGlobals : NormalRel HeapGlobalsRel htrPayloadTxBlock := by
  have pre := heapGlobalsRel_preorder
  unfold htrPayloadTxBlock htrPayloadTxStep htrPayloadTxHashCall htrPayloadTxRelease
  apply normalRel_seq pre
  · apply normalRel_while pre
    apply normalRel_seq pre
    · exact normalRel_discard_call pre _ _ _ _ _ originalRuntimeCode_htrPbytes_lookup
        (NormalRel.returned htrPbytes_normal_heapGlobals)
    · apply normalRel_heapGlobals_leaf
      intro name different
      rfl
  · apply normalRel_seq pre
    · exact htrPlistChunks_call_heapGlobals _
    · exact normalRel_discard_call pre _ _ _ _ _ originalRuntimeCode_heap_release_lookup heapRelease_returned_heapGlobals

/-- The full original transaction block changes the global map exactly by
restoring the saved heap frontier. -/
theorem htrPayload_tx_block_normal_globals {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (mark : BitVec 64)
    (marker : state.locals.lookup (ofString "m2") = some (.val (.word mark)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state htrPayloadTxBlock = (none,post)) :
    post.globals = (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word mark)) state).globals := by
  have frame := normalRel_apply htrPayload_tx_block_heapGlobals (X := state) (by rw [run]; exact Or.inl rfl) code
  rw [run] at frame
  have heap := htrPayload_tx_block_normal_heap state post mark marker code run
  apply HolFiniteMapExact.ext
  funext name
  by_cases same : name = ofString "heap_ptr"
  · subst name
    simpa [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE] using heap
  · simpa [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm same] using frame name same

#print axioms htrPayload_tx_block_heapGlobals
#print axioms htrPayload_tx_block_normal_globals
#print axioms htrPayload_tx_block_local_frame
#print axioms htrPayload_tx_block_normal_heap
end InitECandidate.Runtime
