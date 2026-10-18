import InitECandidate.Runtime.MerkleizeSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def merklePaddingBody : ProgHOL 64 :=
  match merkleizeAt 12 with | .seq (.while _ body) _ => body | _ => .skip

def merklePaddingLoop : ProgHOL 64 :=
  .while (.cmp .less (.var .local (ofString "d")) (.var .local (ofString "target"))) merklePaddingBody

theorem source_merklePadding_body : merklePaddingBody =
    .seq (.call (some (none,none)) (ofString "sha256_pair")
      [.var .local (ofString "buf"),
       .op .add [.var .global (ofString "zero_hashes"),.panop .mul [.var .local (ofString "d"),.const 32]],
       .var .local (ofString "buf")])
      (.assign .local (ofString "d") (.op .add [.var .local (ofString "d"),.const 1])) := by rfl

theorem source_merkleDepth_declaration : merkleizeAt 11 =
    .dec (ofString "d") .one (.var .local (ofString "dn")) (merkleizeAt 12) := by rfl

theorem source_merklePadding : merkleizeAt 12 = .seq merklePaddingLoop (merkleizeAt 13) := by rfl

theorem source_merkleFinish : merkleizeAt 13 =
    .seq (.call (some (none,none)) (ofString "memcpy")
      [.var .local (ofString "out"),.var .local (ofString "buf"),.const 32])
      (.seq (.call (some (none,none)) (ofString "heap_release") [.var .local (ofString "mark")])
        (.return (.const 0))) := by rfl

#print axioms source_merklePadding_body
#print axioms source_merkleDepth_declaration
#print axioms source_merklePadding
#print axioms source_merkleFinish
end InitECandidate.Runtime
