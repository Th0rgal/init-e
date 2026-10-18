import InitECandidate.Runtime.PayloadAllocationFailureBound
import InitECandidate.Runtime.SszFailCallTerminal
import InitECandidate.Runtime.DiscardCallNoReturn
import InitECandidate.Runtime.AllocationReturnedGuard
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- A returned payload decode passed the minimum-length guard and reaches
its initial allocation in the unchanged caller state. -/
theorem payload_body_returned_allocation_entry {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (length : BitVec 64) (value : ValueHOL 64)
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_payload) = (some (.returned value),post)) :
    540 ≤ length.toNat ∧ evaluateHOLFiniteState state (payloadAt 1) = (some (.returned value),post) := by
  rw [source_payload_length_guard,evaluateHOLFiniteState_seq_line780] at run
  unfold payloadLengthGuard at run
  have condition : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.cmp .lower (.var .local (ofString "len")) (.const 540)) =
      some (.val (.word (if length < (540 : BitVec 64) then (1 : BitVec 64) else 0))) := by
    by_cases small : length < (540 : BitVec 64) <;>
      simp [evalHOLExact,lengthLocal,Compiler.Encoders.Asm.wordCmpHOL,small]
  rw [evaluateHOLFiniteState_ite,condition] at run
  by_cases small : length < (540 : BitVec 64)
  · rw [if_pos small] at run
    dsimp only at run
    rw [if_neg (by decide : (1 : BitVec 64) ≠ 0)] at run
    have terminal := evaluate_sszFail_call_terminal state (.const 50) 50 code (by rfl)
    have noReturn := evaluate_discard_call_no_return state (ofString "ssz_fail") [.const 50] value
    cases ran : evaluateHOLFiniteState state (.call (some (none,none)) (ofString "ssz_fail") [.const 50]) with
    | mk result middle =>
      rw [ran] at run terminal noReturn
      cases result with
      | none => exact False.elim (terminal rfl)
      | some result => exact False.elim (noReturn (Prod.mk.inj run).1)
  · rw [if_neg small] at run
    dsimp only at run
    rw [if_pos (rfl : (0 : BitVec 64) = 0),evaluateHOLFiniteState_skip] at run
    refine ⟨?_,run⟩
    change ¬ length.toNat < 540 at small
    omega

/-- Successful payload allocation capacity follows from the actual returned
run, with no assumed future allocation reserve or clock budget. -/
theorem payload_body_returned_allocation_capacity {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (length heap : BitVec 64) (value : ValueHOL 64)
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (within : heap.toNat ≤ 33806089496)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_payload) = (some (.returned value),post)) :
    (136 : BitVec 64) ≤ (33806089496 : BitVec 64) - heap ∧ heap.toNat + 136 ≤ 33806089496 := by
  have bodyRun := (payload_body_returned_allocation_entry state post length value lengthLocal code run).2
  rw [source_payload_allocation] at bodyRun
  have request := alloc_declaration_returned_request state post (.const 136) heap 136 (ofString "pl") .one
    (payloadAt 2) value (by rfl) code heapGlobal bodyRun
  exact ⟨request,allocationGuard_sum_bound heap 136 within request⟩

#print axioms payload_body_returned_allocation_entry
#print axioms payload_body_returned_allocation_capacity
end InitECandidate.Runtime
