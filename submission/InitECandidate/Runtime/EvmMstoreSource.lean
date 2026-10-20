import InitECandidate.Runtime.ChargeWithMemoryDiscardAccessProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def mstoreAt (index : Nat) : ProgHOL 64 :=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_op_mstore)
theorem source_mstore_0 : mstoreAt 0=.decCall (ofString "start") (.comb [.one,.one,.one,.one]) (ofString "stack_pop") [] (mstoreAt 1) :=rfl
theorem source_mstore_1 : mstoreAt 1=.decCall (ofString "value") (.comb [.one,.one,.one,.one]) (ofString "stack_pop") [] (mstoreAt 2) :=rfl
theorem source_mstore_2 : mstoreAt 2=.seq (.call (some (none,none)) (ofString "charge_with_memory") [.const 3,.var .local (ofString "start"),.rstruct [.const 32,.const 0,.const 0,.const 0]]) (mstoreAt 3) :=rfl
theorem source_mstore_3 : mstoreAt 3=.decCall (ofString "s") .one (ofString "sat_word") [.var .local (ofString "start")] (mstoreAt 4) :=rfl
theorem source_mstore_4 : mstoreAt 4=.seq (.call (some (none,none)) (ofString "u256_to_be32") [.var .local (ofString "value"),.op .add [fundingLoad 24,.var .local (ofString "s")]]) (mstoreAt 5) :=rfl
theorem source_mstore_5 : mstoreAt 5=.seq (.call (some (none,none)) (ofString "pc_add") [.const 1]) (mstoreAt 6) :=rfl
theorem source_mstore_6 : mstoreAt 6=.return (.const 0) :=rfl
#print axioms source_mstore_0
#print axioms source_mstore_1
#print axioms source_mstore_2
#print axioms source_mstore_3
#print axioms source_mstore_4
#print axioms source_mstore_5
#print axioms source_mstore_6
end InitECandidate.Runtime
