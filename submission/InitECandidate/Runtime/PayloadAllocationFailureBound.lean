import InitECandidate.Runtime.PayloadShortInputBound
import InitECandidate.Runtime.AllocationFailureDeclarationNoTimeout
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem source_payload_allocation : payloadAt 1 =
    .decCall (ofString "pl") .one (ofString "alloc") [.const 136] (payloadAt 2) := by
  simp only [payloadAt,authorizationNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

/-- Exhausting the real heap rejects at the first decoder allocation within
two source ticks; no reserve for a successful allocation is required. -/
theorem payload_allocation_failure_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (request : ((33806089496 : BitVec 64) - heap).toNat < 136)
    (budget : 2 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (payloadAt 1)
    state.clock ≤ evaluated.2.clock + 2 ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) [.const 136] =
      some [.val (.word (136 : BitVec 64))] := rfl
  have terminal := evaluate_alloc_request_failure_declaration state (.const 136) heap 136
    (ofString "pl") .one (payloadAt 2) args code heapGlobal request
  have noTimeout := evaluate_alloc_request_failure_declaration_no_timeout state (.const 136) heap 136
    (ofString "pl") .one (payloadAt 2) args code heapGlobal request budget
  rw [source_payload_allocation]
  dsimp only
  exact ⟨by rw [terminal.2]; omega,by rw [terminal.2]; omega,noTimeout,terminal.1⟩

/-- Natural heap geometry implies the actual unsigned allocator failure guard. -/
theorem payload_allocation_failure_of_capacity {F : Type} (state : PanSemStateFiniteExact 64 F)
    (heap : BitVec 64) (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (within : heap.toNat ≤ 33806089496) (exhausted : 33806089496 < heap.toNat + 136)
    (budget : 2 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (payloadAt 1)
    state.clock ≤ evaluated.2.clock + 2 ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  apply payload_allocation_failure_bounded state heap code heapGlobal _ budget
  have difference : ((33806089496 : BitVec 64) - heap).toNat = 33806089496 - heap.toNat := by
    rw [BitVec.toNat_sub_of_le]
    · rfl
    · exact within
  rw [difference]
  omega

/-- The full original payload decoder is bounded on initial heap exhaustion,
including its earlier short-input rejection. -/
theorem evaluate_payload_body_allocation_failure_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (length heap : BitVec 64)
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (request : ((33806089496 : BitVec 64) - heap).toNat < 136)
    (budget : 2 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_payload)
    state.clock ≤ evaluated.2.clock + 2 ∧ evaluated.2.clock ≤ state.clock ∧
      evaluated.1 ≠ some .timeOut ∧ evaluated.1 ≠ none := by
  by_cases small : length < (540 : BitVec 64)
  · have bounded := evaluate_payload_short_input_bounded state length lengthLocal small code (by omega)
    exact ⟨by have spent := bounded.1; omega,bounded.2⟩
  · have condition : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .lower (.var .local (ofString "len")) (.const 540)) = some (.val (.word (0 : BitVec 64))) := by
      simp [evalHOLExact,lengthLocal,Compiler.Encoders.Asm.wordCmpHOL]
      change 540 ≤ length.toNat
      change ¬ length.toNat < 540 at small
      omega
    rw [source_payload_length_guard,evaluateHOLFiniteState_seq_line780]
    unfold payloadLengthGuard
    rw [evaluateHOLFiniteState_ite,condition]
    dsimp only
    rw [if_pos (rfl : (0 : BitVec 64) = 0),evaluateHOLFiniteState_skip]
    exact payload_allocation_failure_bounded state heap code heapGlobal request budget

#print axioms payload_allocation_failure_bounded
#print axioms payload_allocation_failure_of_capacity
#print axioms evaluate_payload_body_allocation_failure_bounded
end InitECandidate.Runtime
