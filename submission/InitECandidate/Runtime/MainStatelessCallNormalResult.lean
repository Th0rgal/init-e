import InitECandidate.Runtime.MainStatelessCallBound
import InitECandidate.Runtime.MainSszHandlerTerminal
import InitECandidate.Runtime.PanLocalCallTerminalHandlerNormal
import InitECandidate.Runtime.PanLocalCallNormalResult
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- Normal completion of main's handled call exposes the actual decoder
return, rather than a rejection-handler state. -/
theorem main_stateless_call_normal_result {F : Type}
    (state post : PanSemStateFiniteExact 64 F) (pointer length : BitVec 64)
    (inp : state.locals.lookup (ofString "inp") =
      some (.rStruct [.val (.word pointer),.val (.word length)]))
    (code : state.code = originalRuntimeCode)
    (run : evaluateHOLFiniteState state mainStatelessCall = (none,post)) :
    ∃ value bodyPost,
      evaluateHOLFiniteState (callEntryStateHOLFinite state (statelessInputCallee pointer length))
        (sourceFunctionBody Guest.guestFn_decode_stateless_input) = (some (.returned value),bodyPost) ∧
      shapeEqHOL (shapeOfHOLExact value) .one = true ∧
      post = setVarHOLFinite (ofString "si") value {bodyPost with locals := state.locals} := by
  have args : evalListHOLFinite state (h := fun a => Classical.propDecidable (state.memaddrs a))
      mainStatelessArguments = some [.val (.word pointer),.val (.word length)] := by
    simp [mainStatelessArguments,evalListHOLFinite,evalListHOLExact,evalHOLExact,inp]
  have lookup := pan_two_word_lookup state.code.lookup (ofString "decode_stateless_input")
    (ofString "p") (ofString "len") (sourceFunctionBody Guest.guestFn_decode_stateless_input)
    pointer length (by decide) (by rw [code]; exact originalRuntimeCode_decodeStatelessInput_lookup)
  have normal := evaluate_localCall_terminal_handler_normal_result state post (ofString "si")
    (ofString "decode_stateless_input") .one mainStatelessArguments _
    (sourceFunctionBody Guest.guestFn_decode_stateless_input) mainSszHandler (ofString "SszErr")
    (ofString "err_code") (statelessInputCallee pointer length) args lookup
    (fun current => evaluate_mainSszHandler_terminal current) run
  exact evaluate_localCall_normal_result state post (ofString "si") (ofString "decode_stateless_input")
    .one mainStatelessArguments _ (sourceFunctionBody Guest.guestFn_decode_stateless_input)
    (statelessInputCallee pointer length) args lookup normal

#print axioms main_stateless_call_normal_result
end InitECandidate.Runtime
