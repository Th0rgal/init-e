import InitECandidate.Runtime.MerkleizeSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def shaPairAt (index : Nat) : ProgHOL 64 :=
  (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_sha256_pair)

def shaPairAccelOffset (offset : BitVec 64) : ExpHOL 64 :=
  .op .add [.var .global (ofString "sha_accel"),.const offset]

def shaPairBlockArguments : List (ExpHOL 64) :=
  [.var .global (ofString "sha_st"),shaPairAccelOffset 32]

theorem source_shaPair_init : shaPairAt 0 =
    .seq (.call (some (none,none)) (ofString "sha256_state_init") [.var .global (ofString "sha_st")]) (shaPairAt 1) := by rfl

theorem source_shaPair_copy_a : shaPairAt 1 =
    .seq (.call (some (none,none)) (ofString "memcpy") [shaPairAccelOffset 32,.var .local (ofString "input_a"),.const 32]) (shaPairAt 2) := by rfl

theorem source_shaPair_copy_b : shaPairAt 2 =
    .seq (.call (some (none,none)) (ofString "memcpy") [shaPairAccelOffset 64,.var .local (ofString "input_b"),.const 32]) (shaPairAt 3) := by rfl

theorem source_shaPair_block_first : shaPairAt 3 =
    .seq (.call (some (none,none)) (ofString "sha256_block") shaPairBlockArguments) (shaPairAt 4) := by rfl

theorem source_shaPair_zero : shaPairAt 4 =
    .seq (.call (some (none,none)) (ofString "memzero") [shaPairAccelOffset 32,.const 64]) (shaPairAt 5) := by rfl

theorem source_shaPair_padding : shaPairAt 5 =
    .seq (.storeByte (shaPairAccelOffset 32) (.const 128)) (shaPairAt 6) := by rfl

theorem source_shaPair_length : shaPairAt 6 =
    .seq (.call (some (none,none)) (ofString "st_be64") [shaPairAccelOffset 88,.const 512]) (shaPairAt 7) := by rfl

theorem source_shaPair_block_last : shaPairAt 7 =
    .seq (.call (some (none,none)) (ofString "sha256_block") shaPairBlockArguments) (shaPairAt 8) := by rfl

theorem source_shaPair_finish : shaPairAt 8 =
    .seq (.call (some (none,none)) (ofString "sha256_finish") [.var .global (ofString "sha_st"),.var .local (ofString "out")]) (shaPairAt 9) := by rfl

theorem source_shaPair_return : shaPairAt 9 = .return (.const 0) := by rfl

#print axioms source_shaPair_init
#print axioms source_shaPair_copy_a
#print axioms source_shaPair_copy_b
#print axioms source_shaPair_block_first
#print axioms source_shaPair_zero
#print axioms source_shaPair_padding
#print axioms source_shaPair_length
#print axioms source_shaPair_block_last
#print axioms source_shaPair_finish
#print axioms source_shaPair_return
end InitECandidate.Runtime
