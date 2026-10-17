import InitECandidate.Runtime.RlpHeaderLongStringContract
import InitECandidate.Runtime.RlpHeaderLongStringBodyReader
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original long-string branch exposes its successful concrete reader. -/
theorem rlpHeader_long_string_return_reader {F : Type} (state final : PanSemStateFiniteExact 64 F)
    (pointer header total : BitVec 64) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (headerLocal : state.locals.lookup (ofString "b") = some (.val (.word header)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (lower : 183 < header.toNat) (upper : header.toNat ≤ 191)
    (nonzero : total ≠ 0) (code : state.code = originalRuntimeCode) (ticks : 10 ≤ state.clock)
    (run : evaluateHOLFiniteState state rlpHeaderLongString = (some (.returned value),final)) :
    ∃ (payload : BitVec 64) (readerPost : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState (callEntryStateHOLFinite
        (setVarHOLFinite (ofString "ll") (.val (.word (header - 183))) state)
        (rlpReadLengthCallee (pointer + 1) (header - 183)))
        (sourceFunctionBody Guest.guestFn_rlp_read_length) = (some (.returned (.val (.word payload))),readerPost) ∧
      value = rlpHeaderLongStringValue (header - 183) payload ∧ payload.toNat < total.toNat ∧
      0 < (1 + ((header - 183) + payload)).toNat ∧
      (1 + ((header - 183) + payload)).toNat ≤ total.toNat := by
  have sizeBound := (rlp_header_length_bytes header 183 lower upper).2
  have initializer : @evalHOLExact 64 F _ state.toExact
      (fun address => Classical.propDecidable (state.memaddrs address))
      (.op .sub [.var .local (ofString "b"),.const 183]) = some (.val (.word (header - 183))) := by
    simp [evalHOLExact,evalListHOLExact,headerLocal,wordOpHOL,wordOp,valueIsWord,valueWord]
  rw [source_rlpHeader_long_string] at run
  obtain ⟨output,bodyRun,_⟩ := evaluate_dec_word_result_scope state final (ofString "ll")
    (.op .sub [.var .local (ofString "b"),.const 183]) (header - 183) rlpHeaderLongStringBody
    (some (.returned value)) initializer run
  let entered := setVarHOLFinite (ofString "ll") (.val (.word (header - 183))) state
  have atPointer : entered.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "ll" ≠ ofString "p" by decide] using pointerLocal
  have atLength : entered.locals.lookup (ofString "ll") = some (.val (.word (header - 183))) := by
    simp [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have atTotal : entered.locals.lookup (ofString "len") = some (.val (.word total)) := by
    simpa [entered,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "ll" ≠ ofString "len" by decide] using totalLocal
  exact rlpHeader_long_string_body_return_reader entered output pointer (header - 183) total value
    atPointer atLength atTotal nonzero code (by change (header - 183).toNat + 2 ≤ state.clock; omega) bodyRun

#print axioms rlpHeader_long_string_return_reader
end InitECandidate.Runtime
