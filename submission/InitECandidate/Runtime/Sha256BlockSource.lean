import InitECandidate.Runtime.MerkleizeSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def shaBlockAt (index : Nat) : ProgHOL 64 :=
  (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_sha256_block)

def shaBlockPackBody : ProgHOL 64 :=
  match shaBlockAt 2 with | .seq (.while _ body) _ => body | _ => .skip

def shaBlockUnpackBody : ProgHOL 64 :=
  match shaBlockAt 5 with | .seq (.while _ body) _ => body | _ => .skip

def shaBlockPackLo : ExpHOL 64 :=
  match shaBlockPackBody with | .dec _ _ initializer _ => initializer | _ => .const 0

def shaBlockPackHi : ExpHOL 64 :=
  match shaBlockPackBody with | .dec _ _ _ (.dec _ _ initializer _) => initializer | _ => .const 0

def shaBlockPackValue : ExpHOL 64 :=
  match shaBlockPackBody with | .dec _ _ _ (.dec _ _ _ (.seq (.store _ value) _)) => value | _ => .const 0

theorem source_shaBlock_pack_body : shaBlockPackBody =
    .dec (ofString "lo") .one shaBlockPackLo
      (.dec (ofString "hi") .one shaBlockPackHi
        (.seq (.store (.op .add [.var .global (ofString "sha_accel"),
          .panop .mul [.var .local (ofString "i"),.const 8]]) shaBlockPackValue)
          (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])))) := by rfl

theorem source_shaBlock_copy : shaBlockAt 0 =
    .seq (.ite (.cmp .notEqual (.var .local (ofString "blk"))
      (.op .add [.var .global (ofString "sha_accel"),.const 32]))
      (.call (some (none,none)) (ofString "memcpy")
        [.op .add [.var .global (ofString "sha_accel"),.const 32],.var .local (ofString "blk"),.const 64]) .skip)
      (shaBlockAt 1) := by rfl

theorem source_shaBlock_counter : shaBlockAt 1 =
    .dec (ofString "i") .one (.const 0) (shaBlockAt 2) := by rfl

theorem source_shaBlock_pack : shaBlockAt 2 =
    .seq (.while (.cmp .less (.var .local (ofString "i")) (.const 4)) shaBlockPackBody) (shaBlockAt 3) := by rfl

theorem source_shaBlock_external : shaBlockAt 3 =
    .seq (.extCall (ofString "sha256f") (.var .global (ofString "sha_accel")) (.const 0)
      (.var .global (ofString "sha_accel")) (.const 96)) (shaBlockAt 4) := by rfl

theorem source_shaBlock_reset : shaBlockAt 4 =
    .seq (.assign .local (ofString "i") (.const 0)) (shaBlockAt 5) := by rfl

theorem source_shaBlock_unpack : shaBlockAt 5 =
    .seq (.while (.cmp .less (.var .local (ofString "i")) (.const 4)) shaBlockUnpackBody)
      (.return (.const 0)) := by rfl

#print axioms source_shaBlock_pack_body
#print axioms source_shaBlock_copy
#print axioms source_shaBlock_counter
#print axioms source_shaBlock_pack
#print axioms source_shaBlock_external
#print axioms source_shaBlock_reset
#print axioms source_shaBlock_unpack
end InitECandidate.Runtime
