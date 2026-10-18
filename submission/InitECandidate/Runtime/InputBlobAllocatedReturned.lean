import InitECandidate.Runtime.InputBlobCopyReturned
import InitECandidate.Runtime.AllocationReturnedGuard
import InitECandidate.Runtime.AllocationBodyBound
import InitECandidate.Runtime.PanDecCallReturnedNonzeroClock
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A successful input allocation returns the entry heap pointer and the
declared length; its advanced aligned heap covers the copied bytes plus
the extra eight bytes. Capacity is derived from the returned run. -/
theorem inputBlob_allocated_returned {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (length pointer : BitVec 64) (value : ValueHOL 64)
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (heapBound : pointer.toNat ≤ 33806089496) (small : length.toNat ≤ 134217712)
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (inputBlobAt 3) = (some (.returned value),post)) :
    value = .rStruct [.val (.word pointer),.val (.word length)] ∧
      post.globals = (setGlobalHOLFinite (ofString "heap_ptr")
        (.val (.word (allocationEnd pointer (length + 8)))) state).globals ∧
      (allocationEnd pointer (length + 8)).toNat ≤ 33806089496 ∧
      pointer.toNat + length.toNat + 8 ≤ (allocationEnd pointer (length + 8)).toNat ∧
      (allocationEnd pointer (length + 8)).toNat % 8 = 0 := by
  let argument : ExpHOL 64 := .op .add [.var .local (ofString "len"),.const 8]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [argument] =
      some [.val (.word (length + 8))] := by
    simp [argument,evalListHOLFinite,evalListHOLExact,evalHOLExact,atLength,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_inputBlob_stages.2.2.2.1] at run
  have request := alloc_declaration_returned_request state post argument pointer (length + 8) (ofString "p") .one
    (inputBlobAt 4) value args code heap run
  have nonzero := evaluate_decCall_returned_nonzero_clock state post (ofString "p") (ofString "alloc") .one
    [argument] (inputBlobAt 4) value run
  have bound := allocationEnd_within_heap pointer (length + 8) heapBound request
  obtain ⟨ready,_,_,_,locals,_,_,_,_,globals,declaration⟩ := evaluate_alloc_call_and_declaration state argument pointer
    (length + 8) args code nonzero heap request bound
  have p : (setVarHOLFinite (ofString "p") (.val (.word pointer)) ready).locals.lookup (ofString "p") =
      some (.val (.word pointer)) := by simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have len : (setVarHOLFinite (ofString "p") (.val (.word pointer)) ready).locals.lookup (ofString "len") =
      some (.val (.word length)) := by
    simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,atLength,
      show ofString "p" ≠ ofString "len" by decide]
  have sizeNat : (length + 8).toNat = length.toNat + 8 := by
    rw [BitVec.toNat_add]; simp; omega
  have covered := allocationEnd_covers pointer (length + 8) (allocationGuard_sum_bound pointer _ heapBound request)
  rw [declaration] at run
  cases copyRun : evaluateHOLFiniteState (setVarHOLFinite (ofString "p") (.val (.word pointer)) ready) (inputBlobAt 4) with
  | mk result output =>
    rw [copyRun] at run
    dsimp only at run
    obtain ⟨resultEq,postEq⟩ := Prod.mk.inj run
    subst result
    obtain ⟨returned,kept⟩ := inputBlob_copy_returned _ output pointer length value p len copyRun
    refine ⟨returned,?_,bound,?_,covered.2.2⟩
    · rw [← postEq]
      change output.globals = _
      rw [kept]
      exact globals
    · rw [sizeNat] at covered
      omega

#print axioms inputBlob_allocated_returned
end InitECandidate.Runtime
