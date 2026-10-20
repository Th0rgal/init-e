import InitECandidate.Runtime.ChargeWithMemoryDiscardAccessProgress
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000

def mstore8At (index : Nat) : ProgHOL 64 :=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_op_mstore8)
theorem source_mstore8_0 : mstore8At 0=.decCall (ofString "start") (.comb [.one,.one,.one,.one]) (ofString "stack_pop") [] (mstore8At 1) :=rfl
theorem source_mstore8_1 : mstore8At 1=.decCall (ofString "value") (.comb [.one,.one,.one,.one]) (ofString "stack_pop") [] (mstore8At 2) :=rfl
theorem source_mstore8_2 : mstore8At 2=.seq (.call (some (none,none)) (ofString "charge_with_memory") [.const 3,.var .local (ofString "start"),.rstruct [.const 1,.const 0,.const 0,.const 0]]) (mstore8At 3) :=rfl
theorem source_mstore8_3 : mstore8At 3=.decCall (ofString "s") .one (ofString "sat_word") [.var .local (ofString "start")] (mstore8At 4) :=rfl
theorem source_mstore8_4 : mstore8At 4=.seq (.storeByte (.op .add [fundingLoad 24,.var .local (ofString "s")]) (.op .and [.rfield 0 (.var .local (ofString "value")),.const 255])) (mstore8At 5) :=rfl
theorem source_mstore8_5 : mstore8At 5=.seq (.call (some (none,none)) (ofString "pc_add") [.const 1]) (mstore8At 6) :=rfl
theorem source_mstore8_6 : mstore8At 6=.return (.const 0) :=rfl
#print axioms source_mstore8_0
#print axioms source_mstore8_1
#print axioms source_mstore8_2
#print axioms source_mstore8_3
#print axioms source_mstore8_4
#print axioms source_mstore8_5
#print axioms source_mstore8_6
end InitECandidate.Runtime
