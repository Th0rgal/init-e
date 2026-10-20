import InitECandidate.Runtime.ChargeWithMemoryDiscardAccessProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def mloadAt (index : Nat) : ProgHOL 64 :=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_op_mload)
theorem source_mload_0 : mloadAt 0=.decCall (ofString "start") (.comb [.one,.one,.one,.one]) (ofString "stack_pop") [] (mloadAt 1) :=rfl
theorem source_mload_1 : mloadAt 1=.seq (.call (some (none,none)) (ofString "charge_with_memory") [.const 3,.var .local (ofString "start"),.rstruct [.const 32,.const 0,.const 0,.const 0]]) (mloadAt 2) :=rfl
theorem source_mload_2 : mloadAt 2=.decCall (ofString "s") .one (ofString "sat_word") [.var .local (ofString "start")] (mloadAt 3) :=rfl
theorem source_mload_3 : mloadAt 3=.decCall (ofString "v") (.comb [.one,.one,.one,.one]) (ofString "u256_from_be") [.op .add [fundingLoad 24,.var .local (ofString "s")],.const 32] (mloadAt 4) :=rfl
theorem source_mload_4 : mloadAt 4=.seq (.call (some (none,none)) (ofString "stack_push") [.var .local (ofString "v")]) (mloadAt 5) :=rfl
theorem source_mload_5 : mloadAt 5=.seq (.call (some (none,none)) (ofString "pc_add") [.const 1]) (mloadAt 6) :=rfl
theorem source_mload_6 : mloadAt 6=.return (.const 0) :=rfl
#print axioms source_mload_0
#print axioms source_mload_1
#print axioms source_mload_2
#print axioms source_mload_3
#print axioms source_mload_4
#print axioms source_mload_5
#print axioms source_mload_6
end InitECandidate.Runtime
