import InitECandidate.Runtime.RlpSlicesUpdatesInvariant
import InitECandidate.Runtime.OriginalRlpUncheckedCode
import InitECandidate.Runtime.PanSingleWordLookup
import InitECandidate.Runtime.PanDecCallNormalWordBody
import InitECandidate.Runtime.LocalScopeRestore
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful filling exposes its unchecked callee and exact cursor update. -/
theorem rlpSlices_step_consumed {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer offset index : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (offsetLocal : state.locals.lookup (ofString "off") = some (.val (.word offset)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state rlpSlicesStep = (none,post)) :
    ∃ (consumed : BitVec 64) (bodyPost : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState (callEntryStateHOLFinite state
        (HolFiniteMapExact.empty.update (ofString "p",.val (.word (pointer + offset)))))
        (sourceFunctionBody Guest.guestFn_rlp_item_total_unchecked) = (some (.returned (.val (.word consumed))),bodyPost) ∧
      post.locals.lookup (ofString "off") = some (.val (.word (offset + consumed))) ∧
      post.locals.lookup (ofString "i") = some (.val (.word (index + 1))) := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      [.op .add [.var .local (ofString "p"),.var .local (ofString "off")]] = some [.val (.word (pointer + offset))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,offsetLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  have installed : state.code.lookup (ofString "rlp_item_total_unchecked") =
      some ([(ofString "p",.one)],sourceFunctionBody Guest.guestFn_rlp_item_total_unchecked,.one) := by
    rw [code]; exact originalRuntimeCode_rlpUnchecked_lookup
  have lookup := pan_single_word_lookup state.code.lookup (ofString "rlp_item_total_unchecked") (ofString "p")
    (sourceFunctionBody Guest.guestFn_rlp_item_total_unchecked) (pointer + offset) installed
  rw [source_rlpSlices_step] at run
  obtain ⟨consumed,bodyPost,ready,output,bodyRun,locals,tail,restored⟩ := evaluate_decCall_one_normal_word_body
    state post (ofString "total") (ofString "rlp_item_total_unchecked") _ _ _ rlpSlicesUpdates _ args lookup run
  let entered := setVarHOLFinite (ofString "total") (.val (.word consumed)) ready
  have atOffset : entered.locals.lookup (ofString "off") = some (.val (.word offset)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "total" ≠ ofString "off" by decide] using offsetLocal
  have atIndex : entered.locals.lookup (ofString "i") = some (.val (.word index)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "total" ≠ ofString "i" by decide] using indexLocal
  have atTotal : entered.locals.lookup (ofString "total") = some (.val (.word consumed)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have updates := rlpSlices_updates_normal_locals entered output index offset consumed atIndex atOffset atTotal tail
  refine ⟨consumed,bodyPost,bodyRun,?_,?_⟩
  · rw [restored,restore_other_local _ _ (ofString "off") _ (by decide)]
    exact updates.2.1
  · rw [restored,restore_other_local _ _ (ofString "i") _ (by decide)]
    exact updates.1

#print axioms rlpSlices_step_consumed
end InitECandidate.Runtime
