import InitECandidate.Runtime.RlpItemBodyProgress
import InitECandidate.Runtime.RlpDecodeFullyProgress
import InitECandidate.Runtime.OriginalRlpItemCode
import InitECandidate.Runtime.PanDecCallReturnedBodyScope
import InitECandidate.Runtime.PanEvaluationMetadata
import InitECandidate.Runtime.RlpHeaderCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Successful execution of the complete original full decoder returns a
valid item shape consuming exactly all supplied input. -/
theorem rlpDecodeFully_body_return_contract {F : Type} (state post : PanSemStateFiniteExact 64 F)
    (pointer total : BitVec 64) (finalValue : ValueHOL 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (totalLocal : state.locals.lookup (ofString "len") = some (.val (.word total)))
    (code : state.code = originalRuntimeCode) (ticks : 12 ≤ state.clock)
    (run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_decode_fully) = (some (.returned finalValue),post)) :
    ∃ kind payloadPointer payload : BitVec 64,
      finalValue = .rStruct [.val (.word kind),.val (.word payloadPointer),.val (.word payload),.val (.word total)] ∧
      (kind = 0 ∨ kind = 1) ∧ payload.toNat ≤ total.toNat ∧ 0 < total.toNat := by
  let arguments : List (ExpHOL 64) := [.var .local (ofString "p"),.var .local (ofString "len")]
  have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word total)] := by
    simp [arguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,totalLocal]
  have installed : state.code.lookup (ofString "rlp_item") =
      some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_item,.comb [.one,.one,.one,.one]) := by
    rw [code]; exact originalRuntimeCode_rlpItem_lookup
  have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_item") (ofString "p") (ofString "len")
    (sourceFunctionBody Guest.guestFn_rlp_item) (.comb [.one,.one,.one,.one]) pointer total (by decide) installed
  let callee := rlpHeaderCallee pointer total
  let entry := callEntryStateHOLFinite state callee
  have atPointer : entry.locals.lookup (ofString "p") = some (.val (.word pointer)) := by
    simp [entry,callee,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,
      show ofString "len" ≠ ofString "p" by decide]
  have atTotal : entry.locals.lookup (ofString "len") = some (.val (.word total)) := by
    simp [entry,callee,rlpHeaderCallee,callEntryStateHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  rw [source_rlpDecodeFully_body] at run
  obtain ⟨value,bodyPost,ready,output,bodyRun,locals,_,_,_,readyCode,tail,_⟩ :=
    evaluate_decCall_returned_body_scope state post (ofString "it") (ofString "rlp_item")
      (.comb [.one,.one,.one,.one]) (.comb [.one,.one,.one,.one]) arguments
      [.val (.word pointer),.val (.word total)] (sourceFunctionBody Guest.guestFn_rlp_item)
      rlpDecodeFullyContinuation callee finalValue args lookup run
  obtain ⟨kind,payloadPointer,payload,consumed,fields,flag,payloadBound,positive,consumedBound⟩ :=
    rlpItem_body_return_progress entry bodyPost pointer total value atPointer atTotal code
      (by change 11 ≤ state.clock - 1; omega) bodyRun
  have metadata := evaluateHOLFiniteState_metadata entry (sourceFunctionBody Guest.guestFn_rlp_item)
  rw [bodyRun] at metadata
  dsimp only at metadata
  let resumed := setVarHOLFinite (ofString "it") value ready
  have itemLocal : resumed.locals.lookup (ofString "it") = some
      (.rStruct [.val (.word kind),.val (.word payloadPointer),.val (.word payload),.val (.word consumed)]) := by
    simp [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,fields]
  have totalResumed : resumed.locals.lookup (ofString "len") = some (.val (.word total)) := by
    simpa [resumed,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE,locals,
      show ofString "it" ≠ ofString "len" by decide] using totalLocal
  obtain ⟨returned,matched⟩ := rlpDecodeFully_continuation_return_contract resumed output kind payloadPointer payload consumed total
    finalValue itemLocal totalResumed (readyCode.trans (metadata.1.trans code)) tail
  subst consumed
  exact ⟨kind,payloadPointer,payload,returned,flag,payloadBound,positive⟩

#print axioms rlpDecodeFully_body_return_contract
end InitECandidate.Runtime
