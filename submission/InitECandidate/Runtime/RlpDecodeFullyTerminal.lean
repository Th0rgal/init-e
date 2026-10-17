import InitECandidate.Runtime.RlpDecodeFullyContinuation
import InitECandidate.Runtime.OriginalRlpItemCode
import InitECandidate.Runtime.PanTwoWordLookup
import InitECandidate.Runtime.PanDecCallNormalReturnProperty
import InitECandidate.Runtime.RlpHeaderCallBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The original full decoder never falls through its final check/return,
independently of clock, input readability, or nested validation failures. -/
theorem evaluate_rlpDecodeFully_body_terminal {F : Type} (state : PanSemStateFiniteExact 64 F)
    (pointer length : BitVec 64)
    (pointerLocal : state.locals.lookup (ofString "p") = some (.val (.word pointer)))
    (lengthLocal : state.locals.lookup (ofString "len") = some (.val (.word length)))
    (code : state.code = originalRuntimeCode) :
    (evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_decode_fully)).1 ≠ none := by
  intro normal
  cases run : evaluateHOLFiniteState state (sourceFunctionBody Guest.guestFn_rlp_decode_fully) with
  | mk result post =>
    rw [run] at normal
    change result = none at normal
    subst result
    rw [source_rlpDecodeFully_body] at run
    have args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address))
        [.var .local (ofString "p"),.var .local (ofString "len")] =
        some [.val (.word pointer),.val (.word length)] := by
      simp [evalListHOLFinite,evalListHOLExact,evalHOLExact,pointerLocal,lengthLocal]
    have installed : state.code.lookup (ofString "rlp_item") =
        some ([(ofString "p",.one),(ofString "len",.one)],sourceFunctionBody Guest.guestFn_rlp_item,.comb [.one,.one,.one,.one]) := by
      rw [code]
      exact originalRuntimeCode_rlpItem_lookup
    have lookup := pan_two_word_lookup_shape state.code.lookup (ofString "rlp_item")
      (ofString "p") (ofString "len") (sourceFunctionBody Guest.guestFn_rlp_item)
      (.comb [.one,.one,.one,.one]) pointer length (by decide) installed
    obtain ⟨value,ready,output,_,_,tail,_⟩ := evaluate_decCall_normal_return_property state post
      (ofString "it") (ofString "rlp_item") (.comb [.one,.one,.one,.one]) (.comb [.one,.one,.one,.one])
      [.var .local (ofString "p"),.var .local (ofString "len")] [.val (.word pointer),.val (.word length)]
      (sourceFunctionBody Guest.guestFn_rlp_item) rlpDecodeFullyContinuation (rlpHeaderCallee pointer length)
      args lookup (fun _ => True) (by intro _ _ _; trivial) run
    have terminal := evaluate_rlpDecodeFully_continuation_terminal (setVarHOLFinite (ofString "it") value ready)
    rw [tail] at terminal
    exact terminal rfl

#print axioms evaluate_rlpDecodeFully_body_terminal
end InitECandidate.Runtime
