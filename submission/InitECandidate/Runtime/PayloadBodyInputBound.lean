import InitECandidate.Runtime.PayloadInputHeaderSuffixBound
import InitECandidate.Runtime.PayloadAllocationSuccess
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Initial payload allocation and every subsequent decoder step have an
input-length bound, including exhausted heap and inaccessible input/header cells. -/
theorem evaluate_payload_allocation_suffix_input_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length offsets heapPointer : BitVec 64)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (pointerBound : heapPointer.toNat ≤ 33806089496) (aligned : heapPointer.toNat % 8 = 0)
    (domain0 : state.memaddrs (offsets + 0)) (domain8 : state.memaddrs (offsets + 8))
    (domain16 : state.memaddrs (offsets + 16)) (domain24 : state.memaddrs (offsets + 24))
    (budget : sszSplitBound length + 79 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (payloadAt 1)
    state.clock ≤ evaluated.2.clock + (sszSplitBound length + 79) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  by_cases capacity : heapPointer.toNat + 136 ≤ 33806089496
  · obtain ⟨ready,clock,memory,domain,installed,shapes,endian,pl,locals,globals,endNat,declaration⟩ :=
      payload_allocation_success_entry state heapPointer code heap capacity aligned (by omega)
    have p : ready.locals.lookup (ofString "p") = some (.val (.word pointer)) :=
      (locals _ (by decide)).trans atPointer
    have len : ready.locals.lookup (ofString "len") = some (.val (.word length)) :=
      (locals _ (by decide)).trans atLength
    have offsetsLocal : ready.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)) := by
      rw [globals]
      simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,atOffsets,
        show ofString "heap_ptr" ≠ ofString "ssz_offs" by decide]
    have readyHeap : ready.globals.lookup (ofString "heap_ptr") = some (.val (.word (allocationEnd heapPointer 136))) := by
      rw [globals]
      simp [setGlobalHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
    have bounded := evaluate_payload_input_header_suffix_bounded ready pointer length offsets (allocationEnd heapPointer 136)
      p len offsetsLocal (installed.trans code) readyHeap (by rw [endNat]; exact capacity)
      (by rw [domain]; exact domain0) (by rw [domain]; exact domain8)
      (by rw [domain]; exact domain16) (by rw [domain]; exact domain24)
      (by rw [clock]; omega)
    rw [declaration]
    cases run : evaluateHOLFiniteState ready (payloadAt 2) with
    | mk result post =>
      rw [run] at bounded
      dsimp only at bounded ⊢
      exact ⟨by have consumed := bounded.1; omega,by have remaining := bounded.2.1; omega,bounded.2.2⟩
  · have rejected := payload_allocation_failure_of_capacity state heapPointer code heap pointerBound (by omega) (by omega)
    exact ⟨by have consumed := rejected.1; omega,rejected.2.1,rejected.2.2.1⟩

/-- The complete original decode_payload body uses at most
2*floor(inputLength/4)+81 source clocks. Offset-array domain and initialized
aligned heap are required; malformed payload data and heap exhaustion are covered. -/
theorem evaluate_payload_body_input_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length offsets heapPointer : BitVec 64)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (pointerBound : heapPointer.toNat ≤ 33806089496) (aligned : heapPointer.toNat % 8 = 0)
    (domain0 : state.memaddrs (offsets + 0)) (domain8 : state.memaddrs (offsets + 8))
    (domain16 : state.memaddrs (offsets + 16)) (domain24 : state.memaddrs (offsets + 24))
    (budget : sszSplitBound length + 79 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_decode_payload)
    state.clock ≤ evaluated.2.clock + (sszSplitBound length + 79) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  by_cases small : length < (540 : BitVec 64)
  · have rejected := evaluate_payload_short_input_bounded state length atLength small code (by omega)
    exact ⟨by have consumed := rejected.1; omega,rejected.2.1,rejected.2.2.1⟩
  · have condition : @evalHOLExact 64 F _ state.toExact
        (fun address => Classical.propDecidable (state.memaddrs address))
        (.cmp .lower (.var .local (ofString "len")) (.const 540)) = some (.val (.word (0 : BitVec 64))) := by
      simp [evalHOLExact,atLength,Compiler.Encoders.Asm.wordCmpHOL]
      change 540 ≤ length.toNat
      change ¬ length.toNat < 540 at small
      omega
    rw [source_payload_length_guard,evaluateHOLFiniteState_seq_line780]
    unfold payloadLengthGuard
    rw [evaluateHOLFiniteState_ite,condition]
    dsimp only
    rw [if_pos (rfl : (0 : BitVec 64) = 0),evaluateHOLFiniteState_skip]
    exact evaluate_payload_allocation_suffix_input_bounded state pointer length offsets heapPointer
      atPointer atLength atOffsets code heap pointerBound aligned domain0 domain8 domain16 domain24 budget

#print axioms evaluate_payload_allocation_suffix_input_bounded
#print axioms evaluate_payload_body_input_bounded
end InitECandidate.Runtime
