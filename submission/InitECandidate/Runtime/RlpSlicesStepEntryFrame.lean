import InitECandidate.Runtime.RlpSlicesEarlierEntry
import InitECandidate.Runtime.RlpUncheckedDeclarationFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A full successful slice iteration writes its current entry and retains
an earlier entry through both the unchecked callee and the actual stores. -/
theorem rlpSlices_step_preserves_earlier {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array index pointer offset : BitVec 64)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (offsetLocal : state.locals.lookup (ofString "off") = some (.val (.word offset)))
    (domain0 : state.memaddrs (array + index * 16#64))
    (domain8 : state.memaddrs (array + index * 16#64 + 8#64))
    (earlier count oldPointer oldLength : BitVec 64)
    (ordered : earlier.toNat < index.toNat) (inside : index.toNat < count.toNat)
    (fits : array.toNat + count.toNat * 16 ≤ 2^64)
    (old : RlpSliceEntry state array earlier oldPointer oldLength)
    (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpSlicesStep = (none,post)) :
    ∃ total : BitVec 64, RlpSliceEntry post array index (pointer + offset) total ∧
      RlpSliceEntry post array earlier oldPointer oldLength := by
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
  have oldEntered := RlpSliceEntry.after_frame state entered array earlier oldPointer oldLength old enteredDomain
    (congrFun enteredMemory _) (congrFun enteredMemory _)
  obtain ⟨afterStores,actual,current,previous,_⟩ := evaluate_rlpSlices_updates_preserve_earlier entered array index pointer offset total
    ((localFrame _ (by decide)).trans arrayLocal) ((localFrame _ (by decide)).trans indexLocal)
    ((localFrame _ (by decide)).trans pointerLocal) ((localFrame _ (by decide)).trans offsetLocal) atTotal
    (by rw [enteredDomain]; exact domain0) (by rw [enteredDomain]; exact domain8)
    earlier count oldPointer oldLength ordered inside fits oldEntered
  have same : output = afterStores := (Prod.mk.inj (tail.symm.trans actual)).2
  subst output
  rw [restored]
  exact ⟨total,RlpSliceEntry.after_frame afterStores _ _ _ _ _ current rfl rfl rfl,
    RlpSliceEntry.after_frame afterStores _ _ _ _ _ previous rfl rfl rfl⟩

theorem rlpSlices_step_establishes_entry {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (array index pointer offset : BitVec 64)
    (arrayLocal : state.locals.lookup (ofString "arr") = some (.val (.word array)))
    (indexLocal : state.locals.lookup (ofString "i") = some (.val (.word index)))
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (offsetLocal : state.locals.lookup (ofString "off") = some (.val (.word offset)))
    (domain0 : state.memaddrs (array + index * 16#64))
    (domain8 : state.memaddrs (array + index * 16#64 + 8#64))
    (code : state.code = originalRuntimeCode) (ticks : 11 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpSlicesStep = (none,post)) :
    ∃ total : BitVec 64, RlpSliceEntry post array index (pointer + offset) total := by
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
  rw [restored]
  exact ⟨total,RlpSliceEntry.after_frame afterStores _ _ _ _ _ current rfl rfl rfl⟩

#print axioms rlpSlices_step_establishes_entry

#print axioms rlpSlices_step_preserves_earlier
end InitECandidate.Runtime
