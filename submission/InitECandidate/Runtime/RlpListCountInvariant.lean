import InitECandidate.Runtime.RlpListCountStep
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A normally completed actual list-count iteration retains its input locals,
keeps count and offset bounded, and strictly decreases remaining input. -/
theorem rlpListCount_step_invariant {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length offset count : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (offsetLocal : state.locals.lookup (ofString "off") = some (.val (.word offset)))
    (countLocal : state.locals.lookup (ofString "count") = some (.val (.word count)))
    (countBound : count.toNat ≤ offset.toNat) (offsetBound : offset.toNat ≤ length.toNat)
    (code : state.code = originalRuntimeCode) (ticks : 13 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpListCountStep = (none,post)) :
    ∃ newOffset newCount : BitVec 64,
      post.locals.lookup (ofString "off") = some (.val (.word newOffset)) ∧
      post.locals.lookup (ofString "count") = some (.val (.word newCount)) ∧
      post.locals.lookup (ofString "p") = some (.val (.word pointer)) ∧
      post.locals.lookup (ofString "len") = some (.val (.word length)) ∧
      newCount.toNat ≤ newOffset.toNat ∧ newOffset.toNat ≤ length.toNat ∧
      length.toNat - newOffset.toNat < length.toNat - offset.toNat := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.op .add [.var .local (ofString "p"),.var .local (ofString "off")],
       .op .sub [.var .local (ofString "len"),.var .local (ofString "off")]] =
      some [.val (.word (pointer + offset)),.val (.word (length - offset))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,lengthLocal,offsetLocal,
      wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_rlpListCount_step] at run
  obtain ⟨total,ready,output,positive,bounded,locals,tail,restored⟩ := evaluate_rlpItemTotal_declaration_progress state post
    (ofString "total") _ rlpListCountUpdates (pointer + offset) (length - offset) args code ticks run
  let entered := setVarHOLFinite (ofString "total") (.val (.word total)) ready
  have localFrame : ∀ name, name ≠ ofString "total" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
  have atTotal : entered.locals.lookup (ofString "total") = some (.val (.word total)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have actual := evaluate_rlpListCount_updates entered offset count total
    ((localFrame _ (by decide)).trans offsetLocal) ((localFrame _ (by decide)).trans countLocal) atTotal
  have same := (Prod.mk.inj (tail.symm.trans actual)).2
  have progress := rlpListCount_update_progress offset count total length countBound offsetBound positive bounded
  refine ⟨offset + total,count + 1,?_,?_,?_,?_,progress.2.2.1,progress.2.2.2.1,progress.2.2.2.2⟩
  all_goals rw [restored,same]
  · rw [restore_other_local _ _ (ofString "off") _ (by decide)]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,show ofString "count" ≠ ofString "off" by decide]
  · rw [restore_other_local _ _ (ofString "count") _ (by decide)]
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  · rw [restore_other_local _ _ (ofString "p") _ (by decide)]
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "count" ≠ ofString "p" by decide,show ofString "off" ≠ ofString "p" by decide]
      using (localFrame (ofString "p") (by decide)).trans pointerLocal
  · rw [restore_other_local _ _ (ofString "len") _ (by decide)]
    simpa [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "count" ≠ ofString "len" by decide,show ofString "off" ≠ ofString "len" by decide]
      using (localFrame (ofString "len") (by decide)).trans lengthLocal

#print axioms rlpListCount_step_invariant
end InitECandidate.Runtime
