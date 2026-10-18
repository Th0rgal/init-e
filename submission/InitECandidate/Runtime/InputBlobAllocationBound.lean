import InitECandidate.Runtime.InputBlobCopyBound
import InitECandidate.Runtime.AllocationCall
import InitECandidate.Runtime.AllocationBodyBound
import InitECandidate.Runtime.AllocationFailureDeclarationNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Allocating the bounded input buffer and copying it has a finite source
bound even if the real allocator rejects the request. -/
theorem evaluate_inputBlob_allocation_copy_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (length heapPointer : BitVec 64)
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (small : length.toNat ≤ 134217712) (budget : inputBlobCopyBound length + 2 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (inputBlobAt 3)
    state.clock ≤ evaluated.2.clock + (inputBlobCopyBound length + 2) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  let argument : ExpHOL 64 := .op .add [.var .local (ofString "len"),.const 8]
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a)) [argument] =
      some [.val (.word (length + 8))] := by
    simp [argument,evalListHOLFinite,evalListHOLExact,evalHOLExact,atLength,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_inputBlob_stages.2.2.2.1]
  by_cases request : length + 8 ≤ (33806089496 : BitVec 64) - heapPointer
  · obtain ⟨ready,_,clock,_,locals,_,_,_,_,_,declaration⟩ := evaluate_alloc_call_and_declaration state argument
      heapPointer (length + 8) args code (by omega) heap request
      (allocationEnd_within_heap heapPointer _ heapBound request)
    have len : (setVarHOLFinite (ofString "p") (.val (.word heapPointer)) ready).locals.lookup (ofString "len") =
        some (.val (.word length)) := by
      simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,atLength,
        show ofString "p" ≠ ofString "len" by decide]
    have bounded := evaluate_inputBlob_copy_bounded (setVarHOLFinite (ofString "p") (.val (.word heapPointer)) ready)
      length len small (by change inputBlobCopyBound length ≤ ready.clock; omega)
    change state.clock ≤ (evaluateHOLFiniteState state
        (.decCall (ofString "p") .one (ofString "alloc") [argument] (inputBlobAt 4))).2.clock + _ ∧ _
    rw [declaration]
    cases run : evaluateHOLFiniteState (setVarHOLFinite (ofString "p") (.val (.word heapPointer)) ready) (inputBlobAt 4) with
    | mk result post =>
      rw [run] at bounded
      dsimp only at bounded ⊢
      have spent : ready.clock ≤ post.clock + inputBlobCopyBound length := bounded.1
      have kept : post.clock ≤ ready.clock := bounded.2.1
      exact ⟨by omega,by omega,bounded.2.2⟩
  · have over : ((33806089496 : BitVec 64) - heapPointer).toNat < (length + 8).toNat := by
      rw [BitVec.le_def] at request; omega
    have terminal := evaluate_alloc_request_failure_declaration state argument heapPointer (length + 8)
      (ofString "p") .one (inputBlobAt 4) args code heap over
    have safe := evaluate_alloc_request_failure_declaration_no_timeout state argument heapPointer (length + 8)
      (ofString "p") .one (inputBlobAt 4) args code heap over (by omega)
    change state.clock ≤ (evaluateHOLFiniteState state
        (.decCall (ofString "p") .one (ofString "alloc") [argument] (inputBlobAt 4))).2.clock + _ ∧ _
    exact ⟨by rw [terminal.2]; omega,by rw [terminal.2]; omega,safe⟩

#print axioms evaluate_inputBlob_allocation_copy_bounded
end InitECandidate.Runtime
