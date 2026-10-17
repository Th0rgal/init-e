import InitECandidate.Runtime.RlpReadLengthCallResult
import InitECandidate.Runtime.RlpReadLengthReadFrame
import InitECandidate.Runtime.PanDecCallBodyFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

/-- The real length-reader declaration retains memory and globals through
read-only continuations at every clock, including canonicality rejection. -/
theorem evaluate_rlpReadLength_declaration_frame {F : Type} (state : PanSemStateFiniteExact 64 F)
    (name : MlS) (continuation : ProgHOL 64) (supported : readOnlyMemory continuation = true)
    (arguments : List (ExpHOL 64)) (pointer length : BitVec 64)
    (args : evalListHOLFinite state (h := fun address => Classical.propDecidable (state.memaddrs address)) arguments =
      some [.val (.word pointer),.val (.word length)])
    (code : state.code = originalRuntimeCode) :
    let evaluated := evaluateHOLFiniteState state (.decCall name .one (ofString "rlp_read_length") arguments continuation)
    evaluated.2.memory = state.memory ∧ evaluated.2.globals = state.globals := by
  have installed : state.code.lookup (ofString "rlp_read_length") =
      some ([(ofString "p",.one),(ofString "n",.one)],sourceFunctionBody Guest.guestFn_rlp_read_length,.one) := by
    rw [code]; exact originalRuntimeCode_rlpReadLength_lookup
  have lookup := pan_two_word_lookup state.code.lookup (ofString "rlp_read_length")
    (ofString "p") (ofString "n") (sourceFunctionBody Guest.guestFn_rlp_read_length) pointer length (by decide) installed
  exact evaluate_decCall_body_frame state name (ofString "rlp_read_length") .one .one arguments
    [.val (.word pointer),.val (.word length)] (sourceFunctionBody Guest.guestFn_rlp_read_length) continuation
    (rlpReadLengthCallee pointer length) args lookup
    (evaluate_rlpReadLength_body_frame _ code) supported

#print axioms evaluate_rlpReadLength_declaration_frame
end InitECandidate.Runtime
