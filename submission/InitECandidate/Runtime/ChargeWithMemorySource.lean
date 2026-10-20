import InitECandidate.Runtime.MemoryExtensionSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString
set_option maxRecDepth 100000
set_option maxHeartbeats 2000000
noncomputable def chargeWithMemoryAt (index : Nat) : ProgHOL 64 :=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_charge_with_memory)
theorem source_charge_with_memory_0 : chargeWithMemoryAt 0=
 .decCall (ofString "x") (.comb [.one,.one]) (ofString "extend_memory_cost1")
  [.var .local (ofString "start"),.var .local (ofString "size")] (chargeWithMemoryAt 1) := rfl
theorem source_charge_with_memory_1 : chargeWithMemoryAt 1=
 .decCall (ofString "total") .one (ofString "add_sat")
  [.var .local (ofString "base"),.rfield 0 (.var .local (ofString "x"))] (chargeWithMemoryAt 2) := rfl
theorem source_charge_with_memory_2 : chargeWithMemoryAt 2=
 .seq (.call (some (none,none)) (ofString "charge_gas") [.var .local (ofString "total")]) (chargeWithMemoryAt 3) := rfl
theorem source_charge_with_memory_3 : chargeWithMemoryAt 3=
 .seq (.call (some (none,none)) (ofString "extend_memory") [.rfield 1 (.var .local (ofString "x"))]) (chargeWithMemoryAt 4) := rfl
theorem source_charge_with_memory_4 : chargeWithMemoryAt 4=.return (.const 0) := rfl
#print axioms source_charge_with_memory_0
#print axioms source_charge_with_memory_1
#print axioms source_charge_with_memory_2
#print axioms source_charge_with_memory_3
#print axioms source_charge_with_memory_4
end InitECandidate.Runtime
