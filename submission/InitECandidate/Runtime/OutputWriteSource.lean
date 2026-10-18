import InitECandidate.Runtime.SourceClock
import InitECandidate.Proofs.FrontendCodecComputation
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def outputWriteCondition : ExpHOL 64 :=
  .cmp .lower (.var .local (ofString "i")) (.var .local (ofString "n"))
def outputWriteStore : ProgHOL 64 :=
  .shMemStore .op8 (.op .add [.const 2688614400,.var .local (ofString "i")])
    (.loadByte (.op .add [.var .local (ofString "src"),.var .local (ofString "i")]))
def outputWriteStep : ProgHOL 64 :=
  .seq outputWriteStore
    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1]))
def outputWriteLoop : ProgHOL 64 := .while outputWriteCondition outputWriteStep

theorem source_outputWrite_body : sourceFunctionBody Guest.guestFn_output_write =
    .dec (ofString "i") .one (.const 0) (.seq outputWriteLoop (.return (.const 0))) := by
  simp only [sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

#print axioms source_outputWrite_body
end InitECandidate.Runtime
