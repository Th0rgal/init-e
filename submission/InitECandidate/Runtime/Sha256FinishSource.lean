import InitECandidate.Runtime.MerkleizeSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def shaFinishAt (index : Nat) : ProgHOL 64 :=
  (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_sha256_finish)

def shaFinishBody : ProgHOL 64 :=
  match shaFinishAt 1 with | .seq (.while _ body) _ => body | _ => .skip

def shaFinishArguments : List (ExpHOL 64) :=
  [.op .add [.var .local (ofString "out"),.panop .mul [.var .local (ofString "i"),.const 4]],
   .load .one (.op .add [.var .local (ofString "stp"),.panop .mul [.var .local (ofString "i"),.const 8]])]

theorem source_shaFinish_body : shaFinishBody =
    .seq (.call (some (none,none)) (ofString "st_be32") shaFinishArguments)
      (.assign .local (ofString "i") (.op .add [.var .local (ofString "i"),.const 1])) := by rfl

theorem source_shaFinish_loop : shaFinishAt 1 =
    .seq (.while (.cmp .less (.var .local (ofString "i")) (.const 8)) shaFinishBody) (.return (.const 0)) := by rfl

theorem source_shaFinish_counter : shaFinishAt 0 =
    .dec (ofString "i") .one (.const 0) (shaFinishAt 1) := by rfl

#print axioms source_shaFinish_body
#print axioms source_shaFinish_loop
#print axioms source_shaFinish_counter
end InitECandidate.Runtime
