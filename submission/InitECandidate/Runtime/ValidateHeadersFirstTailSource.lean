import InitECandidate.Runtime.ValidateHeadersFirstSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def validateHeadersHeaderStore : ProgHOL 64 :=
  .store (.op .add [.var .local (ofString "hs"),.panop .mul [.var .local (ofString "i"),.const 8]]) (.var .local (ofString "h"))
def validateHeadersHashOutput : ExpHOL 64 :=
  .op .add [.var .local (ofString "hashes"),.panop .mul [.var .local (ofString "i"),.const 32]]
def validateHeadersHashArguments : List (ExpHOL 64) := validateHeadersDecodeArguments ++ [validateHeadersHashOutput]
def validateHeadersHashCall : ProgHOL 64 :=
  .call (some (none,none)) (ofString "keccak256") validateHeadersHashArguments
def validateHeadersIncrement : ProgHOL 64 :=
  .assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])

theorem source_validate_headers_first_tail : validateHeadersFirstTail =
    .seq validateHeadersHeaderStore (.seq validateHeadersHashCall validateHeadersIncrement) := rfl

#print axioms source_validate_headers_first_tail
end InitECandidate.Runtime
