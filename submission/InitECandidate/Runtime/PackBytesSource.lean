import InitECandidate.Runtime.MerkleizeSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def packBytesAt (index : Nat) : ProgHOL 64 :=
  (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_pack_bytes)

def packBytesCopyArguments : List (ExpHOL 64) :=
  [.var .local (ofString "buf"),.var .local (ofString "p"),.var .local (ofString "n")]

def packBytesZeroArguments : List (ExpHOL 64) :=
  [.op .add [.var .local (ofString "buf"),.var .local (ofString "n")],
    .op .sub [.panop .mul [.var .local (ofString "count"),.const 32],.var .local (ofString "n")]]

theorem source_packBytes_count : packBytesAt 0 =
    .dec (ofString "count") .one (.shift .lsr (.op .add [.var .local (ofString "n"),.const 31]) (.const 5))
      (packBytesAt 1) := by rfl

theorem source_packBytes_alloc : packBytesAt 1 =
    .decCall (ofString "buf") .one (ofString "alloc")
      [.panop .mul [.var .local (ofString "count"),.const 32]] (packBytesAt 2) := by rfl

theorem source_packBytes_copy : packBytesAt 2 =
    .seq (.call (some (none,none)) (ofString "memcpy") packBytesCopyArguments) (packBytesAt 3) := by rfl

theorem source_packBytes_zero : packBytesAt 3 =
    .seq (.call (some (none,none)) (ofString "memzero") packBytesZeroArguments)
      (.return (.rstruct [.var .local (ofString "buf"),.var .local (ofString "count")])) := by rfl

#print axioms source_packBytes_count
#print axioms source_packBytes_alloc
#print axioms source_packBytes_copy
#print axioms source_packBytes_zero
end InitECandidate.Runtime
