import InitECandidate.Runtime.HtrPbytesGlobals
import InitECandidate.Runtime.HtrPbytesMemory
import InitECandidate.Runtime.HtabGrowFrame
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def htrPayloadAt (index : Nat) : ProgHOL 64 :=
  (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_htr_payload)

def htrPayloadTxArguments : List (ExpHOL 64) :=
  [.load .one (.op .add [.var .local (ofString "txs"),.panop .mul [.var .local (ofString "i"),.const 16]]),
    .load .one (.op .add [.var .local (ofString "txs"),.panop .mul [.var .local (ofString "i"),.const 16],.const 8]),
    .op .add [.var .local (ofString "roots"),.panop .mul [.var .local (ofString "i"),.const 32]]]

def htrPayloadTxStep : ProgHOL 64 :=
  .seq (.call (some (none,none)) (ofString "htr_pbytes") htrPayloadTxArguments)
    (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1]))

def htrPayloadTxCondition : ExpHOL 64 :=
  .cmp .less (.var .local (ofString "i")) (.var .local (ofString "ntx"))

theorem source_htrPayload_transactions : htrPayloadAt 21 =
    .seq (.while htrPayloadTxCondition htrPayloadTxStep) (htrPayloadAt 22) := by rfl

#print axioms source_htrPayload_transactions
end InitECandidate.Runtime
