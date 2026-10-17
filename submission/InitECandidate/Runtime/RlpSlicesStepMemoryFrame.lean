import InitECandidate.Runtime.RlpSlicesStepEntryFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Full successful slice iteration preserves every other memory cell. -/
theorem rlpSlices_step_memory_frame {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array index pointer offset : BitVec 64)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (offsetLocal : state.locals.lookup (ofString "off") = some (.val (.word offset)))
    (domain0 : state.memaddrs (array + index * 16#64))
    (domain8 : state.memaddrs (array + index * 16#64 + 8#64))
    (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpSlicesStep = (none,post)) :
    (∀ cell, cell ≠ array + index * 16#64 → cell ≠ array + index * 16#64 + 8#64 → post.memory cell = state.memory cell) := by
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
  obtain ⟨afterStores,actual,current,_,_,frame⟩ := evaluate_rlpSlices_updates_entry_frame entered array index pointer offset total
    ((localFrame _ (by decide)).trans arrayLocal) ((localFrame _ (by decide)).trans indexLocal)
    ((localFrame _ (by decide)).trans pointerLocal) ((localFrame _ (by decide)).trans offsetLocal) atTotal
    (by rw [enteredDomain]; exact domain0) (by rw [enteredDomain]; exact domain8)
  have same : output = afterStores := (Prod.mk.inj (tail.symm.trans actual)).2
  subst output
  rw [restored]
  intro cell different0 different8
  exact (frame cell different0 different8).trans (congrFun enteredMemory cell)

#print axioms rlpSlices_step_memory_frame
end InitECandidate.Runtime
