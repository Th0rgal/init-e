import InitECandidate.Runtime.ValidateHeadersFirstSource
import InitECandidate.Runtime.PanDecCallReturn
import InitECandidate.Runtime.DecodeHeaderZeroFlag
/-!
The parent header record carried by the validation loop's decode call.

The loop body of the frozen validation source is
`.decCall (ofString "h") .one (ofString "decode_header") validateHeadersDecodeArguments
validateHeadersFirstTail`.  Once the callee returns, the frozen semantics binds the
returned word to the loop's `h` local and runs the tail on the callee's memory and
globals with the caller's locals restored.

This module pins that continuation state and proves the carry: the loop body's evaluation
is the tail's evaluation from the continuation state, in which `h` holds the parent record
pointer and the generated state root word of that record is readable at `pointer + 32`.
-/
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

/-- The continuation state of the loop body's decode call: the callee's memory, globals
and domain with the caller's locals restored and the returned word bound to `h`. -/
def validateHeadersContinuation {F : Type} (s post : PanSemStateFiniteExact 64 F) (record : BitVec 64) :
    PanSemStateFiniteExact 64 F :=
  setVarHOLFinite (ofString "h") (.val (.word record)) { post with locals := s.locals }

/-- The loop body's evaluation once the continuation has run. -/
noncomputable def validateHeadersTailRun {F : Type} (s post : PanSemStateFiniteExact 64 F) (record : BitVec 64) :
    Option (PanSemResultExact 64) × PanSemStateFiniteExact 64 F :=
  let output := evaluateHOLFiniteState (validateHeadersContinuation s post record) validateHeadersFirstTail
  (output.1,{output.2 with locals := (HolFiniteMapExact.resVarEq output.2.locals ((ofString "h"),s.locals.lookup (ofString "h")))})

/-- The validation loop's decode call carries the decoded parent header record: the body
evaluation is the tail's evaluation from the continuation state in which `h` holds the
record pointer, and the record's generated state root word is readable there. -/
theorem validate_headers_parent_carry {F : Type} (s post : PanSemStateFiniteExact 64 F)
    (array index pointer length input inputLength : BitVec 64)
    (callee : HolFiniteMapExact MlS (ValueHOL 64)) (returnShape : ShapeHOL)
    (record rooted : BitVec 64)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (entry : RlpSliceInputEntry s array index pointer length input inputLength)
    (lookup : lookupCodeHOLFinite s.code.lookup (ofString "decode_header")
      [.val (.word pointer),.val (.word length)] =
        some (sourceFunctionBody Guest.guestFn_decode_header, callee, returnShape))
    (clock : s.clock ≠ 0)
    (bodyRun : evaluateHOLFiniteState (callEntryStateHOLFinite s callee) (decodeHeaderAt 0) =
      (some (.returned (.val (.word record))),post))
    (remaining : post.clock ≤ (callEntryStateHOLFinite s callee).clock)
    (declared : shapeEqHOL (shapeOfHOLExact (.val (.word record))) .one = true)
    (returned : shapeEqHOL (shapeOfHOLExact (.val (.word record))) returnShape = true)
    (root : post.memory (record + 32#64) = .word rooted) :
    evaluateHOLFiniteState s validateHeadersFirstBody = validateHeadersTailRun s post record ∧
      (validateHeadersContinuation s post record).locals.lookup (ofString "h") = some (.val (.word record)) ∧
      (validateHeadersContinuation s post record).memory (record + 32#64) = .word rooted := by
  have args := eval_validate_headers_decode_arguments s array index pointer length input inputLength atArray atIndex
    entry
  have carried := evaluate_decCall_return_caller_locals s post (ofString "h") (ofString "decode_header") .one
    returnShape validateHeadersDecodeArguments [.val (.word pointer),.val (.word length)]
    (sourceFunctionBody Guest.guestFn_decode_header) validateHeadersFirstTail callee
    (.val (.word record)) args lookup clock (by rw [source_decode_header_body]; exact bodyRun) remaining declared
    returned
  have hLocal : (validateHeadersContinuation s post record).locals.lookup (ofString "h") =
      some (.val (.word record)) := by
    simp [validateHeadersContinuation,setVarHOLFinite,HolFiniteMapExact.lookup_update,FUPDATE]
  have memory : (validateHeadersContinuation s post record).memory = post.memory := by
    simp [validateHeadersContinuation,setVarHOLFinite]
  refine ⟨?_,hLocal,?_⟩
  · rw [source_validate_headers_first_decode]
    exact carried
  · rw [memory]
    exact root

#print axioms validate_headers_parent_carry
end InitECandidate.Runtime
