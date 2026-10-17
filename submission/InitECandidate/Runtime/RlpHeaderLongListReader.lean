import InitECandidate.Runtime.RlpHeaderLongListContract
import InitECandidate.Runtime.RlpHeaderLongListBodyReader
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original long-list branch exposes its successful concrete reader. -/
theorem rlpHeader_long_list_return_reader {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (pointer header total : BitVec 64) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (lower : 247 < header.toNat) (upper : header.toNat ≤ 255)
    (nonzero : total ≠ 0) (code : state.code = originalRuntimeCode) (ticks : 10 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpHeaderLongList = (some (.returned value),final)) :
    ∃ (payload : BitVec 64) (readerPost : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState (callEntryStateHOLFinite
        (setVarHOLFinite (ofString "ll") (.val (.word (header - 247))) state)
        (rlpReadLengthCallee (pointer + 1) (header - 247)))
        (sourceFunctionBody Guest.guestFn_rlp_read_length) = (some (.returned (.val (.word payload))),readerPost) ∧
      value = rlpHeaderLongListValue (header - 247) payload ∧ payload.toNat < total.toNat ∧
      0 < (1 + ((header - 247) + payload)).toNat ∧
      (1 + ((header - 247) + payload)).toNat ≤ total.toNat := by
  have sizeBound := (rlp_header_length_bytes header 247 lower upper).2
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .sub [.var .local (ofString "b"),.const 247]) = some (.val (.word (header - 247))) := by
    simp [evalHOLExact,evalListHOLExact,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_rlpHeader_long_list] at run
  obtain ⟨output,bodyRun,_⟩ := evaluate_dec_word_result_scope state final (ofString "ll")
    (.op .sub [.var .local (ofString "b"),.const 247]) (header - 247) rlpHeaderLongListBody
    (some (.returned value)) initializer run
  let entered := setVarHOLFinite (ofString "ll") (.val (.word (header - 247))) state
  have atPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "ll" ≠ ofString "p" by decide] using pointerLocal
  have atLength : entered.locals.lookup (ofString "ll") = some (.val (.word (header - 247))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atTotal : entered.locals.lookup (ofString "len") = some (.val (.word total)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "ll" ≠ ofString "len" by decide] using totalLocal
  exact rlpHeader_long_list_body_return_reader entered output pointer (header - 247) total value
    atPointer atLength atTotal nonzero code (by change (header - 247).toNat + 2 ≤ state.clock; omega) bodyRun

#print axioms rlpHeader_long_list_return_reader
end InitECandidate.Runtime
