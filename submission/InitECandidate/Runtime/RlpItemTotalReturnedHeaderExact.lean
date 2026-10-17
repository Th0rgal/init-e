import InitECandidate.Runtime.RlpItemTotalBodyProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

theorem rlpItemTotal_body_returned_header_exact {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64) (value : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) (ticks : 12 ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_item_total) = (some (.returned value),post)) :
    ∃ (header payload kind : BitVec 64) (headerPost : PanSemStateFiniteExact 64 F),
      evaluateHOLFiniteState (callEntryStateHOLFinite state (rlpHeaderCallee pointer length))
        (sourceFunctionBody Guest.guestFn_rlp_item_header) =
        (some (.returned (.rStruct [.val (.word header),.val (.word payload),.val (.word kind)])),headerPost) ∧
      value = .val (.word (header + payload)) := by
  let arguments : List (ExpHOL 64) := [.var .local (ofString "p"),.var .local (ofString "len")]
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)] := by
    simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,lengthLocal]
  have installed : state.code.lookup (ofString "rlp_item_header") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_item_header,.comb [.one,.one,.one]) := by
    rw [code]; exact originalRuntimeCode_rlpHeader_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_item_header")
    (ofString "p") (ofString "len") (sourceFunctionBody Guest.guestFn_rlp_item_header) (.comb [.one,.one,.one])
    pointer length (by decide) installed
  rw [source_rlpItemTotal_body] at run
  obtain ⟨parsed,bodyPost,ready,output,bodyRun,_,_,_,_,_,tail,_⟩ := evaluate_decCall_returned_body_scope state post
    (ofString "h") (ofString "rlp_item_header") (.comb [.one,.one,.one]) (.comb [.one,.one,.one]) arguments
    [.val (.word pointer),.val (.word length)] (sourceFunctionBody Guest.guestFn_rlp_item_header) rlpItemTotalContinuation
    (rlpHeaderCallee pointer length) value args lookup run
  let entry := callEntryStateHOLFinite state (rlpHeaderCallee pointer length)
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have atLength : entry.locals.lookup (ofString "len") = some (.val (.word length)) := by
    simp [entry,callEntryStateHOLFinite,rlpHeaderCallee,HolFiniteMapExact.lookup_update,FUPDATE]
  have entryTicks : 11 ≤ entry.clock := by change 11 ≤ state.clock - 1; omega
  have valid : RlpHeaderSizedProgress parsed length :=
    ⟨rlpHeader_uniform_return_progress entry bodyPost pointer length parsed atPointer atLength code entryTicks bodyRun,
      rlpHeader_uniform_return_sizes entry bodyPost pointer length parsed atPointer atLength code entryTicks bodyRun⟩
  obtain ⟨header,payload,kind,shape,_,_,_⟩ := valid.2
  subst parsed
  refine ⟨header,payload,kind,bodyPost,bodyRun,?_⟩
  apply rlpItemTotal_continuation_returned _ output header payload kind value _ tail
  simp [setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]

#print axioms rlpItemTotal_body_returned_header_exact
end InitECandidate.Runtime
