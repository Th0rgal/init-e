import InitECandidate.Runtime.PayloadAllocationSuccess
import InitECandidate.Runtime.PayloadInputHeaderWrites
import InitECandidate.Runtime.PanSeqAssoc
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Allocation and the initial input-header stores compose into the actual
original payload offset-decoding continuation, at a cost of one entry tick. -/
theorem payload_offset_entry {F : Type} (state : PanSemStateFiniteExact 64 F)
    (heap pointer length : BitVec 64)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode)
    (heapGlobal : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heap)))
    (capacity : heap.toNat + 136 ≤ 33806089496) (aligned : heap.toNat % 8 = 0)
    (domain0 : state.memaddrs (heap + 0)) (domain8 : state.memaddrs (heap + 8))
    (nonzero : state.clock ≠ 0) :
    ∃ entry : PanSemStateFiniteExact 64 F,
      entry.clock = state.clock - 1 ∧ entry.memaddrs = state.memaddrs ∧ entry.code = state.code ∧
      entry.locals.lookup (ofString "pl") = some (.val (.word heap)) ∧
      entry.locals.lookup (ofString "p") = some (.val (.word pointer)) ∧
      entry.locals.lookup (ofString "len") = some (.val (.word length)) ∧
      entry.memory (heap + 0) = .word pointer ∧ entry.memory (heap + 8) = .word length ∧
      entry.globals = (setGlobalHOLFinite (ofString "heap_ptr") (.val (.word (allocationEnd heap 136))) state).globals ∧
      evaluateHOLFiniteState state (payloadAt 1) =
        (let output := evaluateHOLFiniteState entry (payloadAt 4)
         (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals
           (ofString "pl",state.locals.lookup (ofString "pl")))})) := by
  obtain ⟨ready,ticks,memory,domain,postCode,shapes,endian,atPayload,locals,globals,endNat,allocation⟩ :=
    payload_allocation_success_entry state heap code heapGlobal capacity aligned nonzero
  let entry := payloadInputHeaderPost ready heap pointer length
  have stores := evaluate_payload_input_header_writes ready heap pointer length atPayload
    ((locals _ (by decide)).trans atPointer) ((locals _ (by decide)).trans atLength)
    (by rw [domain]; exact domain0) (by rw [domain]; exact domain8)
  have continued : evaluateHOLFiniteState ready (payloadAt 2) = evaluateHOLFiniteState entry (payloadAt 4) := by
    rw [source_payload_input_header,← evaluate_seq_assoc]
    change evaluateHOLFiniteState ready (.seq payloadInputHeader (payloadAt 4)) = _
    rw [evaluateHOLFiniteState_seq_line780,stores]
  have readback := payload_input_header_readback ready heap pointer length
  refine ⟨entry,ticks,domain,postCode,atPayload,(locals _ (by decide)).trans atPointer,
    (locals _ (by decide)).trans atLength,readback.1,readback.2,globals,?_⟩
  rw [allocation,continued]

#print axioms payload_offset_entry
end InitECandidate.Runtime
