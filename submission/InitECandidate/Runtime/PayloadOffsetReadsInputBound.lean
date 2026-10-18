import InitECandidate.Runtime.PayloadOffsetStoresInputBound
import InitECandidate.Runtime.PayloadOffsetCheckEntryLocals
import InitECandidate.Runtime.PanDecUniformClockBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The four original offset reads and complete remaining payload decoder
are bounded by input length. Unreadable or malformed initializers terminate
early; no input-byte readability or valid-offset premise is assumed. -/
theorem evaluate_payload_offset_reads_input_bounded {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length offsets heapPointer : BitVec 64)
    (atPointer : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (atLength : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (atOffsets : state.globals.lookup (ofString "ssz_offs") = some (.val (.word offsets)))
    (code : state.code = originalRuntimeCode)
    (heap : state.globals.lookup (ofString "heap_ptr") = some (.val (.word heapPointer)))
    (pointerBound : heapPointer.toNat ≤ 33806089496)
    (domain0 : state.memaddrs (offsets + 0)) (domain8 : state.memaddrs (offsets + 8))
    (domain16 : state.memaddrs (offsets + 16)) (domain24 : state.memaddrs (offsets + 24))
    (budget : sszSplitBound length + 78 ≤ state.clock) :
    let evaluated := evaluateHOLFiniteState state (payloadAt 4)
    state.clock ≤ evaluated.2.clock + (sszSplitBound length + 78) ∧
      evaluated.2.clock ≤ state.clock ∧ evaluated.1 ≠ some .timeOut := by
  rw [source_payload_offset_read_0]
  apply evaluate_dec_one_uniform_clock_bounded state
  intro extra
  rw [source_payload_offset_read_1]
  apply evaluate_dec_one_uniform_clock_bounded (setVarHOLFinite (ofString "o_extra") (.val (.word extra)) state)
  intro txs
  rw [source_payload_offset_read_2]
  apply evaluate_dec_one_uniform_clock_bounded (setVarHOLFinite (ofString "o_txs") (.val (.word txs)) (setVarHOLFinite (ofString "o_extra") (.val (.word extra)) state))
  intro withdrawals
  rw [source_payload_offset_read_3]
  apply evaluate_dec_one_uniform_clock_bounded (setVarHOLFinite (ofString "o_wd") (.val (.word withdrawals)) (setVarHOLFinite (ofString "o_txs") (.val (.word txs)) (setVarHOLFinite (ofString "o_extra") (.val (.word extra)) state)))
  intro balance
  let ready := setVarHOLFinite (ofString "o_bal") (.val (.word balance))
    (setVarHOLFinite (ofString "o_wd") (.val (.word withdrawals))
      (setVarHOLFinite (ofString "o_txs") (.val (.word txs))
        (setVarHOLFinite (ofString "o_extra") (.val (.word extra)) state)))
  have locals : ready.locals = payloadOffsetLocals state.locals extra txs withdrawals balance := rfl
  have p : ready.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    rw [locals,payload_offset_locals_other _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)]
    exact atPointer
  have len : ready.locals.lookup (ofString "len") = some (.val (.word length)) := by
    rw [locals,payload_offset_locals_other _ _ _ _ _ _ (by decide) (by decide) (by decide) (by decide)]
    exact atLength
  apply evaluate_payload_offset_stores_input_bounded ready pointer extra txs withdrawals balance heapPointer offsets length p
    ?_ ?_ ?_ ?_ len atOffsets code heap pointerBound domain0 domain8 domain16 domain24 budget
  all_goals rw [locals]
  all_goals simp [payloadOffsetLocals,HolFiniteMapExact.lookup_update,FUPDATE,
    show ofString "o_txs" ≠ ofString "o_extra" by decide,
    show ofString "o_wd" ≠ ofString "o_extra" by decide,
    show ofString "o_wd" ≠ ofString "o_txs" by decide,
    show ofString "o_bal" ≠ ofString "o_extra" by decide,
    show ofString "o_bal" ≠ ofString "o_txs" by decide,
    show ofString "o_bal" ≠ ofString "o_wd" by decide]

#print axioms evaluate_payload_offset_reads_input_bounded
end InitECandidate.Runtime
