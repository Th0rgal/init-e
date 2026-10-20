import InitECandidate.Runtime.SplitExtensionSource
import InitECandidate.Runtime.TrieBranchSlotStoreWorld
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def splitExtensionCollisionGuard : ProgHOL 64 :=
 .ite (.cmp .notEqual
  (.load .one (.op .add [.var .local (ofString "br"),.const 32,
   .panop .mul [.var .local (ofString "idx"),.const 8]])) (.const 0))
  (.call (some (none,none)) (ofString "mpt_fail") [.const 11]) .skip

def splitExtensionLeafChildBody : ProgHOL 64 :=
 .decCall (ofString "lf") .one (ofString "node_new_leaf")
  [.op .add [.var .local (ofString "rk"),.var .local (ofString "pl"),.const 1],
   .op .sub [.var .local (ofString "kal"),.const 1],
   .var .local (ofString "vptr"),.var .local (ofString "vlen")]
  (branchSlotStore (ofString "br") (ofString "idx") (ofString "lf"))

def splitExtensionIncomingNonempty : ProgHOL 64 :=
 .dec (ofString "idx") .one
  (.loadByte (.op .add [.var .local (ofString "rk"),.var .local (ofString "pl")]))
  (.seq splitExtensionCollisionGuard splitExtensionLeafChildBody)

theorem source_split_extension_incoming : splitExtensionNewSide=
 .ite (.cmp .equal (.var .local (ofString "kal")) (.const 0))
  (branchPayloadStores (ofString "br") (ofString "vptr") (ofString "vlen"))
  splitExtensionIncomingNonempty :=rfl

#print axioms source_split_extension_incoming
end InitECandidate.Runtime
