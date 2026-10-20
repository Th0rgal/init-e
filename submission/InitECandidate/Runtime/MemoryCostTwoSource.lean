import InitECandidate.Runtime.MemoryCostOneSource
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def memoryCostTwoAt (index : Nat) : ProgHOL 64:=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_extend_memory_cost2)

theorem source_memory_cost_two_0 : memoryCostTwoAt 0=.decCall (ofString "a") (.comb [.one,.one]) (ofString "extend_memory_cost1")
 [.var .local (ofString "s1"),.var .local (ofString "n1")] (memoryCostTwoAt 1) := rfl
theorem source_memory_cost_two_1 : memoryCostTwoAt 1=.seq
 (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "a"))) (.const 18446744073709551615))
  (.return (.var .local (ofString "a"))) .skip) (memoryCostTwoAt 2) := rfl
theorem source_memory_cost_two_2 : memoryCostTwoAt 2=.dec (ofString "saved") .one
 (.load .one (fundingAddress 32)) (memoryCostTwoAt 3) := rfl
theorem source_memory_cost_two_3 : memoryCostTwoAt 3=.seq
 (.store (fundingAddress 32) (.op .add [.var .local (ofString "saved"),.rfield 1 (.var .local (ofString "a"))])) (memoryCostTwoAt 4) := rfl
theorem source_memory_cost_two_4 : memoryCostTwoAt 4=.decCall (ofString "b") (.comb [.one,.one]) (ofString "extend_memory_cost1")
 [.var .local (ofString "s2"),.var .local (ofString "n2")] (memoryCostTwoAt 5) := rfl
theorem source_memory_cost_two_5 : memoryCostTwoAt 5=.seq
 (.store (fundingAddress 32) (.var .local (ofString "saved"))) (memoryCostTwoAt 6) := rfl
theorem source_memory_cost_two_6 : memoryCostTwoAt 6=.seq
 (.ite (.cmp .equal (.rfield 0 (.var .local (ofString "b"))) (.const 18446744073709551615))
  (.return (.var .local (ofString "b"))) .skip) (memoryCostTwoAt 7) := rfl
theorem source_memory_cost_two_7 : memoryCostTwoAt 7=.return (.rstruct
 [.op .add [.rfield 0 (.var .local (ofString "a")),.rfield 0 (.var .local (ofString "b"))],
  .op .add [.rfield 1 (.var .local (ofString "a")),.rfield 1 (.var .local (ofString "b"))]]) := rfl
#print axioms source_memory_cost_two_0
#print axioms source_memory_cost_two_7
end InitECandidate.Runtime
