import InitECandidate.Runtime.TrieBranchHeadStoreWorld
import InitECandidate.Runtime.RunAttemptHeadersSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def createBranchTwoLeavesAt (index : Nat) : ProgHOL 64 :=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn__create_branch_from_two_leaves)

def branchPayloadStores (branch value length : MlS) : ProgHOL 64 :=
 .seq (.store (.op .add [.var .local branch,.const 160]) (.var .local value))
  (.store (.op .add [.var .local branch,.const 168]) (.var .local length))

def createBranchLeafSide (key length value valueLength leaf : MlS) : ProgHOL 64 :=
 .ite (.cmp .equal (.var .local length) (.const 0))
  (branchPayloadStores (ofString "br") value valueLength)
  (.decCall leaf .one (ofString "node_new_leaf")
   [.op .add [.var .local key,.const 1],.op .sub [.var .local length,.const 1],
    .var .local value,.var .local valueLength]
   (branchHeadStore (ofString "br") key leaf))

theorem source_create_branch_two_leaves_0 : createBranchTwoLeavesAt 0=
 .decCall (ofString "br") .one (ofString "node_new_branch") [] (createBranchTwoLeavesAt 1) :=rfl

theorem source_create_branch_two_leaves_1 : createBranchTwoLeavesAt 1=
 .seq (createBranchLeafSide (ofString "k1") (ofString "l1") (ofString "v1") (ofString "vl1") (ofString "lf1"))
  (.seq (createBranchLeafSide (ofString "k2") (ofString "l2") (ofString "v2") (ofString "vl2") (ofString "lf2"))
   (.return (.var .local (ofString "br")))) :=rfl

#print axioms source_create_branch_two_leaves_0
#print axioms source_create_branch_two_leaves_1
end InitECandidate.Runtime
