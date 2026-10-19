import InitECandidate.Runtime.MerkleizeSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString

def mixLengthAt (index : Nat) : ProgHOL 64 :=
  (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_mix_in_length)

def mixLengthHashArguments : List (ExpHOL 64) :=
  [.var .local (ofString "root"),.var .global (ofString "ssz_len_chunk"),.var .local (ofString "out")]

theorem source_mixLength_zero : mixLengthAt 0 =
    .seq (.call (some (none,none)) (ofString "memzero") [.var .global (ofString "ssz_len_chunk"),.const 32])
      (mixLengthAt 1) := by rfl

theorem source_mixLength_store : mixLengthAt 1 =
    .seq (.call (some (none,none)) (ofString "st_le64")
      [.var .global (ofString "ssz_len_chunk"),.var .local (ofString "len")]) (mixLengthAt 2) := by rfl

theorem source_mixLength_hash : mixLengthAt 2 =
    .seq (.call (some (none,none)) (ofString "sha256_pair") mixLengthHashArguments)
      (.return (.const 0)) := by rfl

#print axioms source_mixLength_zero
#print axioms source_mixLength_store
#print axioms source_mixLength_hash
end InitECandidate.Runtime
