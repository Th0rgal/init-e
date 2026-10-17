import InitECandidate.Runtime.RlpHeaderLongListBodyContract
import InitECandidate.Runtime.RlpHeaderLongListReadReader
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful availability checking preserves the concrete reader execution. -/
theorem rlpHeader_long_list_body_return_reader {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (pointer headerLength total : BitVec 64) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "ll") = some (.val (.word headerLength)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (nonzero : total ≠ 0) (code : state.code = originalRuntimeCode)
    (ticks : headerLength.toNat + 2 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpHeaderLongListBody = (some (.returned value),final)) :
    ∃ (payload : BitVec 64) (readerPost : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState (callEntryStateHOLFinite state (rlpReadLengthCallee (pointer + 1) headerLength))
        (sourceFunctionBody Guest.guestFn_rlp_read_length) = (some (.returned (.val (.word payload))),readerPost) ∧
      value = rlpHeaderLongListValue headerLength payload ∧ payload.toNat < total.toNat ∧
      0 < (1 + (headerLength + payload)).toNat ∧ (1 + (headerLength + payload)).toNat ≤ total.toNat := by
  have headerFits := rlpHeader_long_list_body_header_fits state final headerLength total value
    headerLocal totalLocal nonzero code (by omega) run
  obtain ⟨result,middle,check,normal,noReturn⟩ := evaluate_rlp_error_check_flow state
    (.cmp .lower (.op .sub [.var .local (ofString "len"),.const 1]) (.var .local (ofString "ll"))) 3 code
  rw [source_rlpHeader_long_list_body,evaluateHOLFiniteState_seq_line780,check] at run
  cases result with
  | some stopped => exact False.elim (noReturn value (Prod.mk.inj run).1)
  | none =>
    have same := normal rfl
    subst middle
    exact rlpHeader_long_list_read_return_reader state final pointer headerLength total value
      pointerLocal headerLocal totalLocal headerFits code ticks run

#print axioms rlpHeader_long_list_body_return_reader
end InitECandidate.Runtime
