import InitECandidate.Runtime.MerkleizeSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def merkleCopyArguments : List (ExpHOL 64) :=
  [.var .local (ofString "buf"),.var .local (ofString "p"),
    .panop .mul [.var .local (ofString "n"),.const 32]]

def merkleZeroArguments : List (ExpHOL 64) :=
  [.op .add [.var .local (ofString "buf"),.panop .mul [.var .local (ofString "n"),.const 32]],
    .panop .mul [.op .sub [.var .local (ofString "size"),.var .local (ofString "n")],.const 32]]

theorem source_merkleCopy : merkleizeAt 7 =
    .seq (.call (some (none,none)) (ofString "memcpy") merkleCopyArguments) (merkleizeAt 8) := by rfl

theorem source_merkleZero : merkleizeAt 8 =
    .seq (.call (some (none,none)) (ofString "memzero") merkleZeroArguments) (merkleizeAt 9) := by rfl

#print axioms source_merkleCopy
#print axioms source_merkleZero
end InitECandidate.Runtime
