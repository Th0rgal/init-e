import InitECandidate.Runtime.SszSplitVarListSlicesBody
import InitECandidate.Runtime.PanThreeWordShapeLookup
import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def sszSplitCalleeLocals (pointer length limit : BitVec 64) : HolFiniteMapExact MlS (ValueHOL 64) :=
  ((HolFiniteMapExact.empty.update (ofString "p",.val (.word pointer))).update
    (ofString "len",.val (.word length))).update (ofString "lim",.val (.word limit))

/-- A returned variable-list declaration exposes the actual slice-array
return, allocation/heap facts, slice cells and external memory frame before
running its continuation. Caller scope exit preserves the continuation output. -/
theorem sszSplitVarList_declaration_returned {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (continuation : ProgHOL 64) (arguments : List (ExpHOL 64))
    (pointer length limit heapPointer : BitVec 64) (finalValue : ValueHOL 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length),.val (.word limit)])
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (pointerBound : heapPointer.toNat ≤ 33806089496)
    (run : evaluateHOLFiniteState state
      (.decCall name (.comb [.one,.one]) (ofString "ssz_split_var_list") arguments continuation) =
      (some (.returned finalValue),post)) :
    ∃ (value : ValueHOL 64) (bodyPost output : PanSemStateFiniteExact 64 F),
      let entry := callEntryStateHOLFinite state (sszSplitCalleeLocals pointer length limit)
      evaluateHOLFiniteState entry (sourceFunctionBody Guest.guestFn_ssz_split_var_list) = (some (.returned value),bodyPost) ∧
      SszSplitVarListReturned entry length limit heapPointer value bodyPost ∧
      SszSplitVarListSlicesReturned entry pointer length heapPointer bodyPost ∧
      evaluateHOLFiniteState (setVarHOLFinite name value {bodyPost with locals := state.locals}) continuation =
        (some (.returned finalValue),output) ∧
      post.memory = output.memory ∧ post.globals = output.globals ∧ post.memaddrs = output.memaddrs := by
  let callee := sszSplitCalleeLocals pointer length limit
  let entry := callEntryStateHOLFinite state callee
  have p : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callee,sszSplitCalleeLocals,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide,show ofString "lim" ≠ ofString "p" by decide]
  have len : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callee,sszSplitCalleeLocals,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "lim" ≠ ofString "len" by decide]
  have lim : entry.locals.lookup (ofString "lim") = some (.val (.word limit)) := by
    simp [entry,callee,sszSplitCalleeLocals,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have bounded := evaluate_sszSplitVarList_body entry pointer length limit heapPointer code p len lim heap pointerBound
  have slices := evaluate_sszSplitVarList_slices entry pointer length limit heapPointer code p len lim heap pointerBound
  have lookup := pan_three_word_shape_lookup state.code.lookup (ofString "ssz_split_var_list")
    (ofString "p") (ofString "len") (ofString "lim") (sourceFunctionBody Guest.guestFn_ssz_split_var_list)
    (.comb [.one,.one]) pointer length limit (by decide) (by decide) (by decide)
    (by rw [code]; exact originalRuntimeCode_sszSplitVarList_lookup)
  obtain ⟨value,bodyPost,output,bodyRun,checked,tail,restored⟩ := evaluate_decCall_checked_returned_exact_scope state post name
    (ofString "ssz_split_var_list") (.comb [.one,.one]) (.comb [.one,.one]) arguments
    [.val (.word pointer),.val (.word length),.val (.word limit)]
    (sourceFunctionBody Guest.guestFn_ssz_split_var_list) continuation callee finalValue args lookup run
  rw [bodyRun] at bounded slices
  dsimp only at bounded slices
  refine ⟨value,bodyPost,output,bodyRun,bounded.2.2.2.2 value rfl,slices value rfl,tail,?_,?_,?_⟩
  all_goals rw [restored]

#print axioms sszSplitVarList_declaration_returned
end InitECandidate.Runtime
