import InitECandidate.Runtime.StatelessInputSource
import InitECandidate.Runtime.AllocationInitializersBound
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def merkleizeAt (index : Nat) : ProgHOL 64 :=
  (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_merkleize)

def merkleLevelBody : ProgHOL 64 :=
  match merkleizeAt 10 with | .seq (.while _ body) _ => body | _ => .skip

def merklePairBody : ProgHOL 64 :=
  match merkleLevelBody with
  | .dec _ _ _ (.dec _ _ _ (.seq (.while _ body) _)) => body
  | _ => .skip

def merklePairLoop : ProgHOL 64 :=
  .while (.cmp .less (.var .local (ofString "j")) (.var .local (ofString "half"))) merklePairBody

theorem source_merklePair_body : merklePairBody =
    .seq (.call (some (none,none)) (ofString "sha256_pair")
      [.op .add [.var .local (ofString "buf"),.panop .mul [.var .local (ofString "j"),.const 64]],
       .op .add [.var .local (ofString "buf"),.panop .mul [.var .local (ofString "j"),.const 64],.const 32],
       .op .add [.var .local (ofString "buf"),.panop .mul [.var .local (ofString "j"),.const 32]]])
      (.assign .local (ofString "j") (.op .add [.var .local (ofString "j"),.const 1])) := by rfl

theorem source_merkleLevel_body : merkleLevelBody =
    .dec (ofString "half") .one (.shift .lsr (.var .local (ofString "cur")) (.const 1))
      (.dec (ofString "j") .one (.const (0#64))
        (.seq merklePairLoop (.assign .local (ofString "cur") (.var .local (ofString "half"))))) := by rfl

theorem source_merkleLevels : merkleizeAt 10 =
    .seq (.while (.cmp .less (.const 1) (.var .local (ofString "cur"))) merkleLevelBody) (merkleizeAt 11) := by rfl

#print axioms source_merklePair_body
#print axioms source_merkleLevel_body
#print axioms source_merkleLevels
end InitECandidate.Runtime
