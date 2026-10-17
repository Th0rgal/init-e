import InitECandidate.Runtime.RlpSlicesInitializationBound
import InitECandidate.Runtime.AllocationBodyBound
import InitECandidate.Runtime.AllocationCall
import InitECandidate.Runtime.AllocationFailureDeclarationNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def rlpSlicesAllocation : ProgHOL 64 :=
  match sourceFunctionBody Guest.guestFn_rlp_list_to_slices with
  | .decCall _ _ _ _ body => body
  | _ => .skip

theorem source_rlpSlices_allocation : rlpSlicesAllocation =
    .decCall (ofString "arr") .one (ofString "alloc")
      [.panop .mul [.var .local (ofString "count"),.const 16]] rlpSlicesInitialized := by
  simp only [rlpSlicesAllocation,rlpSlicesInitialized,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Array allocation followed by the actual initialized slice loop has a
count-linear bound, including rejection of the wrapped 64-bit allocation size. -/
theorem evaluate_rlpSlices_allocation_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer count heapPointer : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (countLocal : state.locals.lookup (ofString "count") = some (.val (.word count)))
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (heapBound : heapPointer.toNat ≤ 33806089496) (code : state.code = originalRuntimeCode)
    (budget : count.toNat * 12 + 2 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state rlpSlicesAllocation
    state.clock ≤ evaluated.2.clock + (count.toNat * 12 + 2) ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  let argument : ExpHOL 64 := .panop .mul [.var .local (ofString "count"),.const 16]
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [argument] =
      some [.val (.word (count * 16))] := by
    simp [argument,evalListHOLFinite,evalListHOLExact,evalHOLExact,countLocal,panOpHOL,valueIsWord,valueWord]
  by_cases request : count * 16 ≤ (33806089496 : BitVec 64) - heapPointer
  · obtain ⟨ready,_,clock,_,locals,readyCode,_,_,_,_,decl⟩ := evaluate_alloc_call_and_declaration state argument heapPointer
      (count * 16) args code (by omega) heap request (allocationEnd_within_heap heapPointer (count * 16) heapBound request)
    let entered := setVarHOLFinite (ofString "arr") (.val (.word heapPointer)) ready
    have atPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
      simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
        show ofString "arr" ≠ ofString "p" by decide] using pointerLocal
    have atCount : entered.locals.lookup (ofString "count") = some (.val (.word count)) := by
      simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
        show ofString "arr" ≠ ofString "count" by decide] using countLocal
    have bound := evaluate_rlpSlices_initialized_bounded entered pointer count atPointer atCount (readyCode.trans code)
      (by change count.toNat * 12 ≤ ready.clock; omega)
    rw [source_rlpSlices_allocation]
    change (let evaluated := evaluateHOLFiniteState state (.decCall (ofString "arr") .one (ofString "alloc") [argument] rlpSlicesInitialized); _) ∧ _
    rw [decl]
    cases run : evaluateHOLFiniteState entered rlpSlicesInitialized with
    | mk result post =>
      rw [run] at bound
      dsimp only at bound ⊢
      have enteredClock : entered.clock = ready.clock := rfl
      exact ⟨by omega,by omega,bound.2.2⟩
  · have rejected : ((33806089496 : BitVec 64) - heapPointer).toNat < (count * 16).toNat := by
      have bad : ¬(count * 16).toNat ≤ ((33806089496 : BitVec 64) - heapPointer).toNat := fun h => request (BitVec.le_def.mpr h)
      omega
    have failure := evaluate_alloc_request_failure_declaration state argument heapPointer (count * 16)
      (ofString "arr") .one rlpSlicesInitialized args code heap rejected
    have safe := evaluate_alloc_request_failure_declaration_no_timeout state argument heapPointer (count * 16)
      (ofString "arr") .one rlpSlicesInitialized args code heap rejected (by omega)
    rw [source_rlpSlices_allocation]
    change (let evaluated := evaluateHOLFiniteState state (.decCall (ofString "arr") .one (ofString "alloc") [argument] rlpSlicesInitialized); _) ∧ _
    dsimp only [argument] at failure safe ⊢
    exact ⟨by omega,by omega,safe,failure.1⟩

#print axioms evaluate_rlpSlices_allocation_bounded
end InitECandidate.Runtime
