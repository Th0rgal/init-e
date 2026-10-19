import InitECandidate.Runtime.ValidateHeadersBuffers
import InitECandidate.Runtime.HeaderRlpFieldInputBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def validateHeadersFirstCondition : ExpHOL 64 :=
  .cmp .less (.var .local (ofString "i")) (.var .local (ofString "n"))
def validateHeadersFirstBody : ProgHOL 64 :=
  match validateHeadersAt 4 with
  | .seq (.while _ body) _ => body
  | _ => .skip

def validateHeadersFirstTail : ProgHOL 64 :=
  match validateHeadersFirstBody with
  | .decCall _ _ _ _ tail => tail
  | _ => .skip

def validateHeadersDecodeArguments : List (ExpHOL 64) := headerRlpFieldArguments

theorem source_validate_headers_index_init : validateHeadersAt 3 =
    .dec (ofString "i") .one (.const 0) (validateHeadersAt 4) := rfl

theorem source_validate_headers_first_loop : validateHeadersAt 4 =
    .seq (.while validateHeadersFirstCondition validateHeadersFirstBody) (validateHeadersAt 5) := rfl

theorem source_validate_headers_first_decode : validateHeadersFirstBody =
    .decCall (ofString "h") .one (ofString "decode_header") validateHeadersDecodeArguments validateHeadersFirstTail := rfl

/-- The actual loop's two loads read the concrete bounded witness slice. -/
theorem eval_validate_headers_decode_arguments {F : Type} (s : PanSemStateFiniteExact 64 F)
    (array index pointer length input inputLength : BitVec 64)
    (atArray : s.locals.lookup (ofString "arr") = some (.val (.word array)))
    (atIndex : s.locals.lookup (ofString "i") = some (.val (.word index)))
    (entry : RlpSliceInputEntry s array index pointer length input inputLength) :
    evalListHOLFinite s (h := fun address => Classical.propDecidable (s.memaddrs address)) validateHeadersDecodeArguments =
      some [.val (.word pointer),.val (.word length)] := by
  exact eval_header_rlp_field_arguments s array index pointer length input inputLength atArray atIndex entry

#print axioms source_validate_headers_index_init
#print axioms source_validate_headers_first_loop
#print axioms source_validate_headers_first_decode
#print axioms eval_validate_headers_decode_arguments
end InitECandidate.Runtime
