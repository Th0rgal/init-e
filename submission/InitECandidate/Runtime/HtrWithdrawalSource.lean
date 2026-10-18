import InitECandidate.Runtime.MerkleizeSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def htrWithdrawalAt (index : Nat) : ProgHOL 64 :=
  (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_htr_withdrawal)

theorem source_htrWithdrawal_mark : htrWithdrawalAt 0 =
    .decCall (ofString "mark") .one (ofString "heap_mark") [] (htrWithdrawalAt 1) := by rfl

theorem source_htrWithdrawal_alloc : htrWithdrawalAt 1 =
    .decCall (ofString "ch") .one (ofString "alloc") [.panop .mul [.const 4,.const 32]] (htrWithdrawalAt 2) := by rfl

theorem source_htrWithdrawal_u64_first : htrWithdrawalAt 2 =
    .seq (.call (some (none,none)) (ofString "htr_u64_at")
      [.var .local (ofString "w"),.var .local (ofString "ch")]) (htrWithdrawalAt 3) := by rfl

theorem source_htrWithdrawal_u64_second : htrWithdrawalAt 3 =
    .seq (.call (some (none,none)) (ofString "htr_u64_at")
      [.op .add [.var .local (ofString "w"),.const 8],.op .add [.var .local (ofString "ch"),.const 32]])
      (htrWithdrawalAt 4) := by rfl

theorem source_htrWithdrawal_vector : htrWithdrawalAt 4 =
    .seq (.call (some (none,none)) (ofString "htr_bytes_vector")
      [.op .add [.var .local (ofString "w"),.const 16],.const 20,
        .op .add [.var .local (ofString "ch"),.const 64]]) (htrWithdrawalAt 5) := by rfl

theorem source_htrWithdrawal_u64_third : htrWithdrawalAt 5 =
    .seq (.call (some (none,none)) (ofString "htr_u64_at")
      [.op .add [.var .local (ofString "w"),.const 36],.op .add [.var .local (ofString "ch"),.const 96]])
      (htrWithdrawalAt 6) := by rfl

theorem source_htrWithdrawal_merkle : htrWithdrawalAt 6 =
    .seq (.call (some (none,none)) (ofString "merkleize")
      [.var .local (ofString "ch"),.const 4,.const 4,.var .local (ofString "out")])
      (.seq (.call (some (none,none)) (ofString "heap_release") [.var .local (ofString "mark")])
        (.return (.const 0))) := by rfl

#print axioms source_htrWithdrawal_mark
#print axioms source_htrWithdrawal_alloc
#print axioms source_htrWithdrawal_u64_first
#print axioms source_htrWithdrawal_u64_second
#print axioms source_htrWithdrawal_vector
#print axioms source_htrWithdrawal_u64_third
#print axioms source_htrWithdrawal_merkle
end InitECandidate.Runtime
