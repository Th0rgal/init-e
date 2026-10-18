import InitECandidate.Runtime.InputBlobAllocatedReturned
import InitECandidate.Runtime.InputBlobGuardBound
import InitECandidate.Runtime.SharedLoadReturnedContinuation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Every successful original input reader returns a bounded-length buffer
at the entry heap pointer. Its actual advanced heap is aligned, capped,
and strictly beyond the input; every other global is unchanged. -/
theorem inputBlob_body_returned {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer : BitVec 64) (value : ValueHOL 64)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word pointer)))
    (heapBound : pointer.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_input_blob) =
      (some (.returned value),post)) :
    ∃ length : BitVec 64, length.toNat ≤ 134217712 ∧
      value = .rStruct [.val (.word pointer),.val (.word length)] ∧
      post.globals = (setGlobalHOLFinite (ofString "heap_ptr")
        (.val (.word (allocationEnd pointer (length + 8)))) state).globals ∧
      (allocationEnd pointer (length + 8)).toNat ≤ 33806089496 ∧
      pointer.toNat + length.toNat + 8 ≤ (allocationEnd pointer (length + 8)).toNat ∧
      (allocationEnd pointer (length + 8)).toNat % 8 = 0 ∧
      post.memaddrs = state.memaddrs ∧ post.code = state.code := by
  have metadata := evaluateHOLFiniteState_metadata state (sourceFunctionBody Guest.guestFn_input_blob)
  rw [run] at metadata
  change evaluateHOLFiniteState state (inputBlobAt 0) = (some (.returned value),post) at run
  rw [source_inputBlob_stages.1] at run
  obtain ⟨initial,bodyPost,_,bodyRun,scope⟩ := evaluate_dec_returned_scope state post (ofString "len") .one
    (.const 0) (inputBlobAt 1) value run
  rw [source_inputBlob_stages.2.1] at bodyRun
  obtain ⟨ready,length,tail,atLength,globals,_,_,installed⟩ := shared_load_returned_continuation
    (setVarHOLFinite (ofString "len") initial state) bodyPost .opW (ofString "len") (.const 1073741832)
    (inputBlobAt 2) value bodyRun
  have readyGlobals : ready.globals = state.globals := globals
  have readyCode : ready.code = originalRuntimeCode := installed.trans code
  rw [source_inputBlob_stages.2.2.1,evaluateHOLFiniteState_seq_line780] at tail
  cases guarded : evaluateHOLFiniteState ready inputBlobGuard with
  | mk result checked =>
    rw [guarded] at tail
    cases result with
    | some result =>
      have noReturn := evaluate_noDirectReturnWhile inputBlobGuard (by rfl) ready value
      rw [guarded] at noReturn
      exact (noReturn (Prod.mk.inj tail).1).elim
    | none =>
      dsimp only at tail
      obtain ⟨small,same⟩ := inputBlob_guard_normal ready checked length atLength readyCode guarded
      subst checked
      obtain ⟨returned,postGlobals,bounded,covers,aligned⟩ := inputBlob_allocated_returned ready bodyPost length pointer value
        atLength (by rw [readyGlobals]; exact heap) heapBound small readyCode tail
      refine ⟨length,small,returned,?_,bounded,covers,aligned,metadata.2.1,metadata.1⟩
      rw [scope]
      change bodyPost.globals = _
      rw [postGlobals]
      simp only [setGlobalHOLFinite,readyGlobals]

#print axioms inputBlob_body_returned
end InitECandidate.Runtime
