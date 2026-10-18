import InitECandidate.Runtime.StatelessInputSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

def mainAt : Nat → ProgHOL 64
  | 0 => sourceFunctionBody Guest.guestFn_main
  | n + 1 => statelessNext (mainAt n)

def mainSszSerializeArguments : List (ExpHOL 64) :=
  [.var .local (ofString "out"),.var .local (ofString "z32"),.const 0,.const 0,.const 0]
def mainSszOutputArguments : List (ExpHOL 64) :=
  [.var .local (ofString "out"),.op .add [.var .local (ofString "n"),.const 1]]
def mainSszErrorStore : ProgHOL 64 :=
  .storeByte (.op .add [.var .local (ofString "out"),.var .local (ofString "n")])
    (.var .local (ofString "err_code"))
def mainSszHalt : ProgHOL 64 :=
  .seq (.extCall (ofString "halt") .baseAddr (.const 0) .baseAddr (.const 0)) (.return (.const 1))
def mainSszOutput : ProgHOL 64 :=
  .seq mainSszErrorStore (.seq (.call (some (none,none)) (ofString "output_write") mainSszOutputArguments) mainSszHalt)
def mainSszHandler : ProgHOL 64 :=
  .decCall (ofString "n") .one (ofString "serialize_result") mainSszSerializeArguments mainSszOutput
def mainStatelessArguments : List (ExpHOL 64) :=
  [.rfield 0 (.var .local (ofString "inp")),.rfield 1 (.var .local (ofString "inp"))]

theorem source_main_stateless_call : mainAt 20 =
    .seq (.call (some (some (.local,ofString "si"),some (ofString "SszErr",ofString "err_code",mainSszHandler)))
      (ofString "decode_stateless_input") mainStatelessArguments) (mainAt 21) := by
  simp only [mainAt,statelessNext,sourceFunctionBody,
    InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_main_stateless_call
end InitECandidate.Runtime
