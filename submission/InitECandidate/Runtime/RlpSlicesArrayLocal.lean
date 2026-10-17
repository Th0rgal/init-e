import InitECandidate.Runtime.RlpSlicesUpdatesInvariant
import InitECandidate.Runtime.RlpUncheckedDeclarationNormal
import InitECandidate.Runtime.LocalScopeRestore
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normal slice iterations retain the array base across the helper result
scope, stores, index increment and offset increment. -/
theorem rlpSlices_step_array_local {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer offset index array : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (offsetLocal : state.locals.lookup (ofString "off") = some (.val (.word offset)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state rlpSlicesStep = (none,post)) :
    post.locals.lookup (ofString "arr") = some (.val (.word array)) := by
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
  have atArray := (others (ofString "arr") (by decide) (by decide)).trans ((frame _ (by decide)).trans arrayLocal)
  rw [restored]
  change (HolFiniteMapExact.resVarEq output.locals (ofString "total",state.locals.lookup (ofString "total"))).lookup (ofString "arr") = _
  rw [restore_other_local _ _ _ _ (by decide)]
  exact atArray

#print axioms rlpSlices_step_array_local
end InitECandidate.Runtime
