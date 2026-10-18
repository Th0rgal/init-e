import InitECandidate.Runtime.InputBlobReturned
import InitECandidate.Runtime.OriginalInputBlobCode
import InitECandidate.Runtime.PanNoArgsShapeLookup
import InitECandidate.Runtime.PanDecCallCheckedReturnedExactScope
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Main's actual input declaration resumes with the copied input pair and
an aligned capped heap beyond the input. No future allocation reserve is
assumed, and all nonallocator globals are retained. -/
theorem inputBlob_declaration_returned {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (name : MlS) (continuation : ProgHOL 64) (pointer : BitVec 64) (finalValue : ValueHOL 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (heapBound : pointer.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state
      (.decCall name (.comb [.one,.one]) (ofString "input_blob") [] continuation) = (some (.returned finalValue),post)) :
    ∃ (length nextHeap : BitVec 64) (ready output : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState ready continuation = (some (.returned finalValue),output) ∧
      ready.locals = state.locals.update (name,.rStruct [.val (.word pointer),.val (.word length)]) ∧
      ready.code = state.code ∧ ready.memaddrs = state.memaddrs ∧ length.toNat ≤ 134217712 ∧
      ready.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) ∧
      nextHeap.toNat ≤ 33806089496 ∧ nextHeap.toNat % 8 = 0 ∧
      pointer.toNat + length.toNat + 8 ≤ nextHeap.toNat ∧ pointer.toNat + length.toNat < 2 ^ 64 ∧
      (∀ key, key ≠ ofString "heap_ptr" → ready.globals.lookup key = state.globals.lookup key) ∧
      post.memory = output.memory ∧ post.globals = output.globals ∧ post.memaddrs = output.memaddrs := by
  let entry := callEntryStateHOLFinite state HolFiniteMapExact.empty
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [] = some [] := by
    simp [evalListHOLFinite,evalListHOLExact]
  have lookup := pan_no_args_shape_lookup state.code.lookup (ofString "input_blob")
    (sourceFunctionBody Guest.guestFn_input_blob) (.comb [.one,.one])
    (by rw [code]; exact originalRuntimeCode_inputBlob_lookup)
  obtain ⟨value,bodyPost,output,bodyRun,_,tail,restored⟩ := evaluate_decCall_checked_returned_exact_scope state post name
    (ofString "input_blob") (.comb [.one,.one]) (.comb [.one,.one]) [] []
    (sourceFunctionBody Guest.guestFn_input_blob) continuation HolFiniteMapExact.empty finalValue args lookup run
  obtain ⟨length,small,returned,globals,bounded,covers,aligned,domain,installed⟩ :=
    inputBlob_body_returned entry bodyPost pointer value heap heapBound code bodyRun
  rw [returned] at tail
  let nextHeap := allocationEnd pointer (length + 8)
  let ready := setVarHOLFinite name (.rStruct [.val (.word pointer),.val (.word length)])
    {bodyPost with locals := state.locals}
  have nextGlobal : ready.globals.lookup (ofString "heap_ptr") = some (.val (.word nextHeap)) := by
    change bodyPost.globals.lookup _ = _
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,nextHeap]
  have other : ∀ key, key ≠ ofString "heap_ptr" → ready.globals.lookup key = state.globals.lookup key := by
    intro key different
    change bodyPost.globals.lookup key = state.globals.lookup key
    rw [globals]
    simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,Ne.symm different,entry,callEntryStateHOLFinite]
  refine ⟨length,nextHeap,ready,output,tail,rfl,installed,domain,small,nextGlobal,bounded,aligned,covers,
    by omega,other,?_,?_,?_⟩
  all_goals rw [restored]

#print axioms inputBlob_declaration_returned
end InitECandidate.Runtime
