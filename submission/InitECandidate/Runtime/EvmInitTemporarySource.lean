import InitECandidate.Runtime.InitializerCounterSource
import InitECandidate.Runtime.ByteStorePrefixReach
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def evmTransferLiteralStores : List (ExpHOL 64 × ExpHOL 64) := [
  (.var .local (ofString "s"),.const 84),
  (.op .add [.var .local (ofString "s"),.const 1],.const 114),
  (.op .add [.var .local (ofString "s"),.const 2],.const 97),
  (.op .add [.var .local (ofString "s"),.const 3],.const 110),
  (.op .add [.var .local (ofString "s"),.const 4],.const 115),
  (.op .add [.var .local (ofString "s"),.const 5],.const 102),
  (.op .add [.var .local (ofString "s"),.const 6],.const 101),
  (.op .add [.var .local (ofString "s"),.const 7],.const 114),
  (.op .add [.var .local (ofString "s"),.const 8],.const 40),
  (.op .add [.var .local (ofString "s"),.const 9],.const 97),
  (.op .add [.var .local (ofString "s"),.const 10],.const 100),
  (.op .add [.var .local (ofString "s"),.const 11],.const 100),
  (.op .add [.var .local (ofString "s"),.const 12],.const 114),
  (.op .add [.var .local (ofString "s"),.const 13],.const 101),
  (.op .add [.var .local (ofString "s"),.const 14],.const 115),
  (.op .add [.var .local (ofString "s"),.const 15],.const 115),
  (.op .add [.var .local (ofString "s"),.const 16],.const 44),
  (.op .add [.var .local (ofString "s"),.const 17],.const 97),
  (.op .add [.var .local (ofString "s"),.const 18],.const 100),
  (.op .add [.var .local (ofString "s"),.const 19],.const 100),
  (.op .add [.var .local (ofString "s"),.const 20],.const 114),
  (.op .add [.var .local (ofString "s"),.const 21],.const 101),
  (.op .add [.var .local (ofString "s"),.const 22],.const 115),
  (.op .add [.var .local (ofString "s"),.const 23],.const 115),
  (.op .add [.var .local (ofString "s"),.const 24],.const 44),
  (.op .add [.var .local (ofString "s"),.const 25],.const 117),
  (.op .add [.var .local (ofString "s"),.const 26],.const 105),
  (.op .add [.var .local (ofString "s"),.const 27],.const 110),
  (.op .add [.var .local (ofString "s"),.const 28],.const 116),
  (.op .add [.var .local (ofString "s"),.const 29],.const 50),
  (.op .add [.var .local (ofString "s"),.const 30],.const 53),
  (.op .add [.var .local (ofString "s"),.const 31],.const 54),
  (.op .add [.var .local (ofString "s"),.const 32],.const 41)]

theorem source_evmInit_temporary_mark : evmInitAt 0 =
    .decCall (ofString "mark") .one (ofString "heap_mark") [] (evmInitAt 1) := by
  simp only [evmInitAt,statelessNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_evmInit_temporary_allocation : evmInitAt 1 =
    .decCall (ofString "s") .one (ofString "alloc") [.const 40] (evmInitAt 2) := by
  simp only [evmInitAt,statelessNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_evmInit_literal_stores : evmInitAt 2 =
    byteStorePrefix evmTransferLiteralStores (evmInitAt 35) := by
  simp only [evmInitAt,statelessNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem source_evmInit_temporary_release : evmInitAt 35 =
    .seq (.call (some (none,none)) (ofString "heap_release") [.var .local (ofString "mark")]) (evmInitAt 36) := by
  simp only [evmInitAt,statelessNext,sourceFunctionBody,InitECandidate.Proofs.FrontendCodecComputation.declToHOL_eq]
  rfl

theorem evaluate_evmInit_literal_stores_reaches {F : Type} (state : PanSemStateFiniteExact 64 F) :
    Reaches state (evmInitAt 2) (ByteStoreControlFrame state) 0 (evmInitAt 35) := by
  rw [source_evmInit_literal_stores]
  exact evaluate_byteStore_prefix_reaches state evmTransferLiteralStores (evmInitAt 35)

#print axioms source_evmInit_temporary_mark
#print axioms source_evmInit_temporary_allocation
#print axioms source_evmInit_literal_stores
#print axioms source_evmInit_temporary_release
#print axioms evaluate_evmInit_literal_stores_reaches
end InitECandidate.Runtime
