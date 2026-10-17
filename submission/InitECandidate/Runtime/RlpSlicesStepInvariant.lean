import InitECandidate.Runtime.RlpSlicesUpdatesInvariant
import InitECandidate.Runtime.RlpUncheckedDeclarationNormal
import InitECandidate.Runtime.LocalScopeRestore
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every normally completed original slice iteration advances its index,
retains its fixed count and input pointer, and decreases remaining slices. -/
theorem rlpSlices_step_normal_invariant {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer offset index count : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (offsetLocal : state.locals.lookup (ofString "off") = some (.val (.word offset)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (countLocal : state.locals.lookup (ofString "count") = some (.val (.word count)))
    (enabled : index.toNat < count.toNat) (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state rlpSlicesStep = (none,post)) :
    ∃ nextOffset : BitVec 64,
      post.locals.lookup (ofString "off") = some (.val (.word nextOffset)) ∧
      post.locals.lookup (ofString "i") = some (.val (.word (index + 1))) ∧
      post.locals.lookup (ofString "count") = some (.val (.word count)) ∧
      post.locals.lookup (ofString "p") = some (.val (.word pointer)) ∧
      (index + 1).toNat ≤ count.toNat ∧ count.toNat - (index + 1).toNat < count.toNat - index.toNat := by
  rw [source_rlpSlices_step] at run
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.op .add [.var .local (ofString "p"),.var .local (ofString "off")]] = some [.val (.word (pointer + offset))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,offsetLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  obtain ⟨total,ready,output,locals,tail,restored⟩ := evaluate_rlpUnchecked_declaration_normal state post (ofString "total")
    [.op .add [.var .local (ofString "p"),.var .local (ofString "off")]] rlpSlicesUpdates (pointer + offset) args code run
  let entered := setVarHOLFinite (ofString "total") (.val (.word total)) ready
  have frame : ∀ name, name ≠ ofString "total" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
  have atTotal : entered.locals.lookup (ofString "total") = some (.val (.word total)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  obtain ⟨atIndex,atOffset,others⟩ := rlpSlices_updates_normal_locals entered output index offset total
    ((frame _ (by decide)).trans indexLocal) ((frame _ (by decide)).trans offsetLocal) atTotal tail
  have atCount := (others (ofString "count") (by decide) (by decide)).trans ((frame _ (by decide)).trans countLocal)
  have atPointer := (others (ofString "p") (by decide) (by decide)).trans ((frame _ (by decide)).trans pointerLocal)
  have progress := rlpSlices_index_progress index count enabled
  rw [restored]
  refine ⟨offset + total,?_,?_,?_,?_,progress.2.1,progress.2.2⟩
  · change (HolFiniteMapExact.resVarEq output.locals (ofString "total",state.locals.lookup (ofString "total"))).lookup (ofString "off") = _
    rw [restore_other_local _ _ _ _ (by decide)]
    exact atOffset
  · change (HolFiniteMapExact.resVarEq output.locals (ofString "total",state.locals.lookup (ofString "total"))).lookup (ofString "i") = _
    rw [restore_other_local _ _ _ _ (by decide)]
    exact atIndex
  · change (HolFiniteMapExact.resVarEq output.locals (ofString "total",state.locals.lookup (ofString "total"))).lookup (ofString "count") = _
    rw [restore_other_local _ _ _ _ (by decide)]
    exact atCount
  · change (HolFiniteMapExact.resVarEq output.locals (ofString "total",state.locals.lookup (ofString "total"))).lookup (ofString "p") = _
    rw [restore_other_local _ _ _ _ (by decide)]
    exact atPointer

#print axioms rlpSlices_step_normal_invariant
end InitECandidate.Runtime
