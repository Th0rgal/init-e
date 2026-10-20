import InitECandidate.Runtime.CreateBranchTwoLeavesSource
import InitECandidate.Runtime.TrieBranchNibbleStorePathsWorld
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def splitExtensionAt (index : Nat) : ProgHOL 64 :=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn__split_extension)

def splitExtensionSingleChild : ProgHOL 64 :=
 .ite (.cmp .equal (.var .local (ofString "sal")) (.const 1))
  (branchNibbleStore (ofString "br") (ofString "seg") (ofString "pl") (ofString "child")) .skip

def splitExtensionLongChild : ProgHOL 64 :=
 .ite (.cmp .lower (.const 1) (.var .local (ofString "sal")))
  (.decCall (ofString "ex") .one (ofString "node_new_ext")
   [.op .add [.var .local (ofString "seg"),.var .local (ofString "pl"),.const 1],
    .op .sub [.var .local (ofString "sal"),.const 1],.var .local (ofString "child")]
   (branchNibbleStore (ofString "br") (ofString "seg") (ofString "pl") (ofString "ex"))) .skip

def splitExtensionNewSide : ProgHOL 64 :=
 .ite (.cmp .equal (.var .local (ofString "kal")) (.const 0))
  (branchPayloadStores (ofString "br") (ofString "vptr") (ofString "vlen"))
  (.dec (ofString "idx") .one
   (.loadByte (.op .add [.var .local (ofString "rk"),.var .local (ofString "pl")]))
   (.seq
    (.ite (.cmp .notEqual
     (.load .one (.op .add [.var .local (ofString "br"),.const 32,
      .panop .mul [.var .local (ofString "idx"),.const 8]])) (.const 0))
     (.call (some (none,none)) (ofString "mpt_fail") [.const 11]) .skip)
    (.decCall (ofString "lf") .one (ofString "node_new_leaf")
     [.op .add [.var .local (ofString "rk"),.var .local (ofString "pl"),.const 1],
      .op .sub [.var .local (ofString "kal"),.const 1],
      .var .local (ofString "vptr"),.var .local (ofString "vlen")]
     (.store (.op .add [.var .local (ofString "br"),.const 32,
      .panop .mul [.var .local (ofString "idx"),.const 8]]) (.var .local (ofString "lf"))))))

theorem source_split_extension_0 : splitExtensionAt 0=
 .dec (ofString "seg") .one (.load .one (.op .add [.var .local (ofString "node"),.const 32])) (splitExtensionAt 1) :=rfl

theorem source_split_extension_1 : splitExtensionAt 1=
 .dec (ofString "sl") .one (.load .one (.op .add [.var .local (ofString "node"),.const 40])) (splitExtensionAt 2) :=rfl

theorem source_split_extension_2 : splitExtensionAt 2=
 .dec (ofString "child") .one (.load .one (.op .add [.var .local (ofString "node"),.const 48])) (splitExtensionAt 3) :=rfl

theorem source_split_extension_3 : splitExtensionAt 3=
 .decCall (ofString "br") .one (ofString "node_new_branch") [] (splitExtensionAt 4) :=rfl

theorem source_split_extension_4 : splitExtensionAt 4=
 .dec (ofString "sal") .one (.op .sub [.var .local (ofString "sl"),.var .local (ofString "pl")]) (splitExtensionAt 5) :=rfl

theorem source_split_extension_5 : splitExtensionAt 5=
 .seq splitExtensionSingleChild (splitExtensionAt 6) :=rfl

theorem source_split_extension_6 : splitExtensionAt 6=
 .seq splitExtensionLongChild (splitExtensionAt 7) :=rfl

theorem source_split_extension_7 : splitExtensionAt 7=
 .dec (ofString "kal") .one (.op .sub [.var .local (ofString "rl"),.var .local (ofString "pl")]) (splitExtensionAt 8) :=rfl

theorem source_split_extension_8 : splitExtensionAt 8=
 .seq splitExtensionNewSide (.return (.var .local (ofString "br"))) :=rfl

#print axioms source_split_extension_0
#print axioms source_split_extension_7
end InitECandidate.Runtime
