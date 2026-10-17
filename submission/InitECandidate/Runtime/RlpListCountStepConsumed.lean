import InitECandidate.Runtime.LocalScopeRestore
import InitECandidate.Runtime.RlpListCountStep
import InitECandidate.Runtime.RlpItemTotalDeclarationBodyProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successful counting iteration retains its concrete checked item run
and the exact cursor/count updates caused by its returned size. -/
theorem rlpListCount_step_consumed {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length offset count : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (offsetLocal : state.locals.lookup (ofString "off") = some (.val (.word offset)))
    (countLocal : state.locals.lookup (ofString "count") = some (.val (.word count)))
    (code : state.code = originalRuntimeCode) (ticks : 13 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpListCountStep = (none,post)) :
    ∃ (consumed : BitVec 64) (bodyPost : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState (callEntryStateHOLFinite state (rlpHeaderCallee (pointer + offset) (length - offset)))
        (sourceFunctionBody Guest.guestFn_rlp_item_total) = (some (.returned (.val (.word consumed))),bodyPost) ∧
      0 < consumed.toNat ∧ consumed.toNat ≤ (length - offset).toNat ∧
      post.locals.lookup (ofString "off") = some (.val (.word (offset + consumed))) ∧
      post.locals.lookup (ofString "count") = some (.val (.word (count + 1))) := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.op .add [.var .local (ofString "p"),.var .local (ofString "off")],
       .op .sub [.var .local (ofString "len"),.var .local (ofString "off")]] =
      some [.val (.word (pointer + offset)),.val (.word (length - offset))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,lengthLocal,offsetLocal,
      wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_rlpListCount_step] at run
  obtain ⟨consumed,bodyPost,ready,output,bodyRun,positive,bounded,locals,tail,restored⟩ :=
    evaluate_rlpItemTotal_declaration_body_progress state post (ofString "total") _ rlpListCountUpdates
      (pointer + offset) (length - offset) args code ticks run
  let entered := setVarHOLFinite (ofString "total") (.val (.word consumed)) ready
  have atOffset : entered.locals.lookup (ofString "off") = some (.val (.word offset)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "total" ≠ ofString "off" by decide] using offsetLocal
  have atCount : entered.locals.lookup (ofString "count") = some (.val (.word count)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "total" ≠ ofString "count" by decide] using countLocal
  have atTotal : entered.locals.lookup (ofString "total") = some (.val (.word consumed)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have updates := evaluate_rlpListCount_updates entered offset count consumed atOffset atCount atTotal
  have outputEq := (Prod.mk.inj (tail.symm.trans updates)).2
  refine ⟨consumed,bodyPost,bodyRun,positive,bounded,?_,?_⟩
  all_goals rw [restored,outputEq]
  · rw [restore_other_local _ _ (ofString "off") _ (by decide)]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "count" ≠ ofString "off" by decide]
  · rw [restore_other_local _ _ (ofString "count") _ (by decide)]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms rlpListCount_step_consumed
end InitECandidate.Runtime
