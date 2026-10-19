import InitECandidate.Runtime.ValidateHeadersGuard
import InitECandidate.Runtime.OriginalValidateHeadersCode
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

/-! The second loop of the original `validate_headers` (Guest/Ast.lean:6725):
`i := 1; while (i < n) { eq := memeq(load(load(hs + i*8) + 8), hashes + (i-1)*32, 32);
if eq == 0 { raise BlockErr 2 }; i := i + 1 }`.  Everything below names the
exact AST node of `Guest.guestFn_validate_headers`: `validateHeadersSecondAt`
is the same `statelessNext` descent (dec/decCall/seq bodies) the other
`validate_headers` modules use. -/

/-- The node reached from the real function body by `k` `statelessNext` steps.
This is the shared `validateHeadersAt` descent (ValidateHeadersGuard), named
locally so this module's statements read independently of that file. -/
abbrev validateHeadersSecondAt (index : Nat) : ProgHOL 64 := validateHeadersAt index

/-- `i < n`, the actual second-loop guard. -/
def validateHeadersSecondCondition : ExpHOL 64 :=
  .cmp .less (.var .local (ofString "i")) (.var .local (ofString "n"))

/-- `load(load(hs + i*8) + 8)`, the recorded hash of header `i - 1`. -/
def validateHeadersSecondLeftArgument : ExpHOL 64 :=
  .load .one (.op .add [.load .one (.op .add [.var .local (ofString "hs"),
    .panop .mul [.var .local (ofString "i"), .const 8]]), .const 8])

/-- `hashes + (i-1)*32`, the freshly computed digest of header `i - 1`. -/
def validateHeadersSecondRightArgument : ExpHOL 64 :=
  .op .add [.var .local (ofString "hashes"),
    .panop .mul [.op .sub [.var .local (ofString "i"), .const 1], .const 32]]

/-- The actual `memeq` argument list: two pointers and the size `32`. -/
def validateHeadersSecondArguments : List (ExpHOL 64) :=
  [validateHeadersSecondLeftArgument, validateHeadersSecondRightArgument, .const 32]

/-- `if eq == 0 { raise BlockErr 2 }`. -/
def validateHeadersSecondGuard : ProgHOL 64 :=
  .ite (.cmp .equal (.var .local (ofString "eq")) (.const 0))
    (.raise (ofString "BlockErr") (.const 2)) .skip

/-- The actual loop body: the `memeq` declaration call and its continuation. -/
def validateHeadersSecondBody : ProgHOL 64 :=
  .decCall (ofString "eq") .one (ofString "memeq") validateHeadersSecondArguments
    (.seq validateHeadersSecondGuard
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"), .const 1])))

/-- The actual second loop. -/
def validateHeadersSecondLoop : ProgHOL 64 :=
  .while validateHeadersSecondCondition validateHeadersSecondBody

/-- The actual statement after the second loop. -/
def validateHeadersSecondReturn : ProgHOL 64 :=
  .return (.rstruct [.var .local (ofString "hs"), .var .local (ofString "hashes")])

def validateHeadersSecondTail : ProgHOL 64 :=
  .seq validateHeadersSecondLoop validateHeadersSecondReturn

theorem source_validate_headers_second_index_reset :
    validateHeadersSecondAt 5 = .seq (.assign .local (ofString "i") (.const 1)) (validateHeadersSecondAt 6) := rfl

theorem source_validate_headers_second_loop :
    validateHeadersSecondAt 6 = validateHeadersSecondTail := rfl

/-- The real second loop and the real `return (hs, hashes)` that follows it. -/
theorem source_validate_headers_second_body :
    validateHeadersSecondAt 6 = .seq (.while validateHeadersSecondCondition validateHeadersSecondBody)
      validateHeadersSecondReturn := rfl

/-- The real `i := 1` initialisation followed by the real second loop. -/
theorem source_validate_headers_second_tail :
    validateHeadersSecondAt 5 =
      .seq (.assign .local (ofString "i") (.const 1)) validateHeadersSecondTail := rfl

#print axioms source_validate_headers_second_index_reset
#print axioms source_validate_headers_second_loop
#print axioms source_validate_headers_second_body
#print axioms source_validate_headers_second_tail
end InitECandidate.Runtime
