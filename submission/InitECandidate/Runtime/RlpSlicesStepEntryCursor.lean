import InitECandidate.Runtime.RlpSlicesStepEntryFrame
import InitECandidate.Runtime.LocalScopeRestore
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpSlices_step_entry_cursor {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array index pointer offset : BitVec 64)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (offsetLocal : state.locals.lookup (ofString "off") = some (.val (.word offset)))
    (domain0 : state.memaddrs (array + index * 16#64))
    (domain8 : state.memaddrs (array + index * 16#64 + 8#64))
    (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpSlicesStep = (none,post)) :
    ∃ total : BitVec 64, RlpSliceEntry post array index (pointer + offset) total ∧
      post.locals.lookup (ofString "off") = some (.val (.word (offset + total))) := by
  rw [source_rlpSlices_step] at run
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
      [.op .add [.var .local (ofString "p"),.var .local (ofString "off")]] = some [.val (.word (pointer + offset))] := by
    simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,offsetLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  obtain ⟨total,ready,output,locals,memory,_,domain,_,tail,restored⟩ := evaluate_rlpUnchecked_declaration_normal_frame
    state post (ofString "total") _ rlpSlicesUpdates (pointer + offset) args code ticks run
  let entered := setVarHOLFinite (ofString "total") (.val (.word total)) ready
  have localFrame : ∀ name, name ≠ ofString "total" → entered.locals.lookup name = state.locals.lookup name := by
    intro name different
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,locals]
  have atTotal : entered.locals.lookup (ofString "total") = some (.val (.word total)) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have enteredDomain : entered.memaddrs = state.memaddrs := domain
  have enteredMemory : entered.memory = state.memory := memory
  obtain ⟨afterStores,actual,current,_,_,_⟩ := evaluate_rlpSlices_updates_entry_frame entered array index pointer offset total
    ((localFrame _ (by decide)).trans arrayLocal) ((localFrame _ (by decide)).trans indexLocal)
    ((localFrame _ (by decide)).trans pointerLocal) ((localFrame _ (by decide)).trans offsetLocal) atTotal
    (by rw [enteredDomain]; exact domain0) (by rw [enteredDomain]; exact domain8)
  have same : output = afterStores := (Prod.mk.inj (tail.symm.trans actual)).2
  subst output
  have updated := rlpSlices_updates_normal_locals entered afterStores index offset total
    ((localFrame _ (by decide)).trans indexLocal) ((localFrame _ (by decide)).trans offsetLocal) atTotal actual
  rw [restored]
  refine ⟨total,RlpSliceEntry.after_frame afterStores _ _ _ _ _ current rfl rfl rfl,?_⟩
  rw [restore_other_local _ _ (ofString "off") _ (by decide)]
  exact updated.2.1

#print axioms rlpSlices_step_entry_cursor
end InitECandidate.Runtime
