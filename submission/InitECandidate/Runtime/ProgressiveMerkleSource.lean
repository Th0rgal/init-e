import InitECandidate.Runtime.MerkleizeSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def progressiveAt (index : Nat) : ProgHOL 64 :=
  (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_merkleize_progressive)

def progressiveStep : ProgHOL 64 :=
  match progressiveAt 6 with | .seq (.while _ body) _ => body | _ => .skip

def progressiveClip : ProgHOL 64 :=
  match progressiveStep with | .dec _ _ _ (.seq first _) => first | _ => .skip

def progressiveAfterClip : ProgHOL 64 :=
  match progressiveStep with | .dec _ _ _ (.seq _ tail) => tail | _ => .skip

def progressiveUpdates : ProgHOL 64 :=
  match progressiveAfterClip with | .seq _ tail => tail | _ => .skip

def progressiveMerkleArguments : List (ExpHOL 64) :=
  [.op .add [.var .local (ofString "p"),.panop .mul [.var .local (ofString "off"),.const 32]],
   .var .local (ofString "cnt"),.var .local (ofString "size"),
   .op .add [.var .local (ofString "roots"),.panop .mul [.var .local (ofString "k"),.const 32]]]

def progressiveCondition : ExpHOL 64 :=
  .cmp .lower (.var .local (ofString "off")) (.var .local (ofString "n"))

theorem source_progressive_loop : progressiveAt 6 =
    .seq (.while progressiveCondition progressiveStep) (progressiveAt 7) := by rfl

theorem source_progressive_step : progressiveStep =
    .dec (ofString "cnt") .one (.op .sub [.var .local (ofString "n"),.var .local (ofString "off")])
      (.seq progressiveClip progressiveAfterClip) := by rfl

theorem source_progressive_clip : progressiveClip =
    .ite (.cmp .lower (.var .local (ofString "size")) (.var .local (ofString "cnt")))
      (.assign .local (ofString "cnt") (.var .local (ofString "size"))) .skip := by rfl

theorem source_progressive_after_clip : progressiveAfterClip =
    .seq (.call (some (none,none)) (ofString "merkleize") progressiveMerkleArguments) progressiveUpdates := by rfl

theorem source_progressive_updates : progressiveUpdates =
    .seq (.assign .local (ofString "off") (.op .add [.var .local (ofString "off"),.var .local (ofString "size")]))
      (.seq (.assign .local (ofString "size") (.shift .lsl (.var .local (ofString "size")) (.const 2)))
        (.assign .local (ofString "k") (.op .add [.var .local (ofString "k"),.const 1]))) := by rfl

#print axioms source_progressive_loop
#print axioms source_progressive_step
#print axioms source_progressive_clip
#print axioms source_progressive_after_clip
#print axioms source_progressive_updates
end InitECandidate.Runtime
