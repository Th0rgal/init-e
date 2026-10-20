import InitECandidate.Runtime.RunAttemptHeadersSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def mptInsertLeafAt (index : Nat) : ProgHOL 64 :=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn__insert_into_leaf)

def mptInsertLeafEqualReturn : ProgHOL 64 :=
 match mptInsertLeafAt 2 with | .seq (.ite _ (.decCall _ _ _ _ tail) _) _=>tail | _=>.skip

theorem source_mpt_insert_leaf_0 : mptInsertLeafAt 0=
 .dec (ofString "ek") .one (.load .one (.op .add [.var .local (ofString "node"),.const 32])) (mptInsertLeafAt 1) := rfl

theorem source_mpt_insert_leaf_1 : mptInsertLeafAt 1=
 .dec (ofString "el") .one (.load .one (.op .add [.var .local (ofString "node"),.const 40])) (mptInsertLeafAt 2) := rfl

theorem source_mpt_insert_leaf_2 : mptInsertLeafAt 2=
 .seq (.ite (.cmp .equal (.var .local (ofString "el")) (.var .local (ofString "rl")))
  (.decCall (ofString "eq") .one (ofString "memeq")
   [.var .local (ofString "ek"),.var .local (ofString "rk"),.var .local (ofString "el")] mptInsertLeafEqualReturn) .skip)
  (mptInsertLeafAt 3) := rfl

theorem source_mpt_insert_leaf_3 : mptInsertLeafAt 3=
 .decCall (ofString "pl") .one (ofString "common_prefix_length")
  [.var .local (ofString "ek"),.var .local (ofString "el"),.var .local (ofString "rk"),.var .local (ofString "rl")]
  (mptInsertLeafAt 4) := rfl

theorem source_mpt_insert_leaf_4 : mptInsertLeafAt 4=
 .decCall (ofString "br") .one (ofString "_create_branch_from_two_leaves")
  [.op .add [.var .local (ofString "ek"),.var .local (ofString "pl")],
   .op .sub [.var .local (ofString "el"),.var .local (ofString "pl")],
   .load .one (.op .add [.var .local (ofString "node"),.const 48]),
   .load .one (.op .add [.var .local (ofString "node"),.const 56]),
   .op .add [.var .local (ofString "rk"),.var .local (ofString "pl")],
   .op .sub [.var .local (ofString "rl"),.var .local (ofString "pl")],
   .var .local (ofString "vptr"),.var .local (ofString "vlen")] (mptInsertLeafAt 5) := rfl

theorem source_mpt_insert_leaf_5 : mptInsertLeafAt 5=
 .seq (.ite (.cmp .lower (.const 0) (.var .local (ofString "pl")))
  (.call none (ofString "node_new_ext")
   [.var .local (ofString "ek"),.var .local (ofString "pl"),.var .local (ofString "br")]) .skip)
  (.return (.var .local (ofString "br"))) := rfl

#print axioms source_mpt_insert_leaf_2
#print axioms source_mpt_insert_leaf_5
end InitECandidate.Runtime
