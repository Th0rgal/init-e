import InitECandidate.Runtime.StoreLE32Memory
import InitECandidate.Runtime.PanDiscardReturnMemory
import InitECandidate.Runtime.MarkedHeapReturn
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def storeLE64FirstArguments : List (ExpHOL 64) :=
  [.var .local (ofString "p"),.var .local (ofString "v")]
def storeLE64LastArguments : List (ExpHOL 64) :=
  [.op .add [.var .local (ofString "p"),.const 4],.shift .lsr (.var .local (ofString "v")) (.const 32)]

theorem source_storeLE64_body : sourceFunctionBody Guest.guestFn_st_le64 =
    .seq (.call (some (none,none)) (ofString "st_le32") storeLE64FirstArguments)
      (.seq (.call (some (none,none)) (ofString "st_le32") storeLE64LastArguments) (.return (.const 0))) := by
  rw [sourceFunctionBody_eq_structural]; rfl

theorem storeLE64_body_returned_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer value watched : BitVec 64) (returned : ValueHOL 64)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atValue : state.locals.lookup (ofString "v") = some (.val (.word value)))
    (separate : ∀ offset : Nat, offset < 8 → watched ≠ panByteAlignHOL (pointer + BitVec.ofNat 64 offset))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_st_le64) = (some (.returned returned),post)) :
    post.memory watched = state.memory watched := by
  rw [source_storeLE64_body] at run
  obtain ⟨middle,normal,tail⟩ := seq_returned_of_nonreturning_first
    (fun v => evaluate_discard_call_no_return state (ofString "st_le32") storeLE64FirstArguments v) run
  have frame := storeLE32_call_normal_memory state middle storeLE64FirstArguments pointer value watched
    (by simp [storeLE64FirstArguments,evalListHOLExact,evalHOLExact,atPointer,atValue]) code
    (fun offset inside => separate offset (by omega)) normal
  have keep (key : MlS) : middle.locals.lookup key = state.locals.lookup key := by
    have locals := evaluate_avoidsLocal_flowing key (.call (some (none,none)) (ofString "st_le32") storeLE64FirstArguments)
      rfl state (by rw [normal]; exact Or.inl rfl)
    simpa only [normal] using locals
  have installed := evaluateHOLFiniteState_metadata state (.call (some (none,none)) (ofString "st_le32") storeLE64FirstArguments)
  rw [normal] at installed
  obtain ⟨last,called,memory⟩ := evaluate_discard_then_return_memory middle post (ofString "st_le32")
    storeLE64LastArguments (.return (.const 0)) returned rfl tail
  have atP := (keep (ofString "p")).trans atPointer
  have atV := (keep (ofString "v")).trans atValue
  have lastSeparate : ∀ offset : Nat, offset < 4 →
      watched ≠ panByteAlignHOL ((pointer + (4#64)) + BitVec.ofNat 64 offset) := by
    intro offset inside
    have shifted : (pointer + (4#64)) + BitVec.ofNat 64 offset = pointer + BitVec.ofNat 64 (offset + 4) := by
      rw [BitVec.ofNat_add,BitVec.add_assoc]
      congr 1
      exact BitVec.add_comm _ _
    rw [shifted]
    exact separate (offset + 4) (by omega)
  have lastFrame := storeLE32_call_normal_memory middle last storeLE64LastArguments
    (pointer + (4#64)) (value >>> 32) watched
    (by simp [storeLE64LastArguments,evalListHOLExact,evalHOLExact,atP,atV,
      wordOpHOL,wordOp,valueIsWord,valueWord,wordShiftHOL]) (installed.1.trans code) lastSeparate called
  exact (congrFun memory watched).trans (lastFrame.trans frame)

theorem storeLE64_call_normal_memory {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (arguments : List (ExpHOL 64)) (pointer value watched : BitVec 64)
    (args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) arguments =
      some [.val (.word pointer),.val (.word value)]) (code : state.code = originalRuntimeCode)
    (separate : ∀ offset : Nat, offset < 8 → watched ≠ panByteAlignHOL (pointer + BitVec.ofNat 64 offset))
    (run : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "st_le64") arguments) = (none,post)) :
    post.memory watched = state.memory watched := by
  have installed : state.code.lookup (ofString "st_le64") =
      some ([(ofString "p",.one),(ofString "v",.one)],sourceFunctionBody Guest.guestFn_st_le64,.one) := by
    rw [code]; exact vmLookup_st_le64
  have lookup := pan_two_word_lookup state.code.lookup (ofString "st_le64") (ofString "p") (ofString "v")
    (sourceFunctionBody Guest.guestFn_st_le64) pointer value (by decide) installed
  obtain ⟨returned,output,bodyRun,_,postEq⟩ := evaluate_discardCall_normal_result state post (ofString "st_le64")
    .one arguments _ _ _ args lookup run
  rw [postEq]
  let entry := callEntryStateHOLFinite state
    ((HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))).update (ofString "v",.val (.word value)))
  exact storeLE64_body_returned_memory entry output pointer value watched returned
    (by simp (config := {decide := true}) [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE])
    (by simp [entry,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]) separate code bodyRun

#print axioms source_storeLE64_body
#print axioms storeLE64_body_returned_memory
#print axioms storeLE64_call_normal_memory
end InitECandidate.Runtime
