import InitECandidate.Runtime.MemoryCeil32AlignedReturned
namespace InitECandidate.Runtime
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

def memoryCostOneAt (index : Nat) : ProgHOL 64:=
 (statelessNext^[index]) (structuralFunctionBody Guest.guestFn_extend_memory_cost1)

theorem source_memory_cost_one_0 : memoryCostOneAt 0=.decCall (ofString "z") .one (ofString "u256_is_zero")
 [.var .local (ofString "size")] (memoryCostOneAt 1) := rfl
theorem source_memory_cost_one_1 : memoryCostOneAt 1=.seq
 (.ite (.cmp .notEqual (.var .local (ofString "z")) (.const 0))
  (.return (.rstruct [.const 0,.const 0])) .skip) (memoryCostOneAt 2) := rfl
theorem source_memory_cost_one_2 : memoryCostOneAt 2=.decCall (ofString "s") .one (ofString "sat_word")
 [.var .local (ofString "start")] (memoryCostOneAt 3) := rfl
theorem source_memory_cost_one_3 : memoryCostOneAt 3=.decCall (ofString "n") .one (ofString "sat_word")
 [.var .local (ofString "size")] (memoryCostOneAt 4) := rfl
theorem source_memory_cost_one_4 : memoryCostOneAt 4=.decCall (ofString "endp") .one (ofString "add_sat")
 [.var .local (ofString "s"),.var .local (ofString "n")] (memoryCostOneAt 5) := rfl
theorem source_memory_cost_one_5 : memoryCostOneAt 5=.seq
 (.ite (.cmp .equal (.var .local (ofString "endp")) (.const 18446744073709551615))
  (.return (.rstruct [.const 18446744073709551615,.const 0])) .skip) (memoryCostOneAt 6) := rfl

theorem source_memory_cost_one_6 : memoryCostOneAt 6=.dec (ofString "cur") .one
 (.load .one (fundingAddress 32)) (memoryCostOneAt 7) := rfl
theorem source_memory_cost_one_7 : memoryCostOneAt 7=.decCall (ofString "before") .one (ofString "ceil32")
 [.var .local (ofString "cur")] (memoryCostOneAt 8) := rfl
theorem source_memory_cost_one_8 : memoryCostOneAt 8=.decCall (ofString "after") .one (ofString "ceil32")
 [.var .local (ofString "endp")] (memoryCostOneAt 9) := rfl

theorem source_memory_cost_one_9 : memoryCostOneAt 9=.seq
 (.ite (.cmp .notLower (.var .local (ofString "before")) (.var .local (ofString "after")))
  (.return (.rstruct [.const 0,.const 0])) .skip) (memoryCostOneAt 10) := rfl
theorem source_memory_cost_one_10 : memoryCostOneAt 10=.decCall (ofString "ca") .one (ofString "memory_gas_cost")
 [.var .local (ofString "after")] (memoryCostOneAt 11) := rfl
theorem source_memory_cost_one_11 : memoryCostOneAt 11=.decCall (ofString "cb") .one (ofString "memory_gas_cost")
 [.var .local (ofString "before")] (memoryCostOneAt 12) := rfl
theorem source_memory_cost_one_12 : memoryCostOneAt 12=.seq
 (.ite (.cmp .equal (.var .local (ofString "ca")) (.const 18446744073709551615))
  (.return (.rstruct [.const 18446744073709551615,.const 0])) .skip) (memoryCostOneAt 13) := rfl
theorem source_memory_cost_one_13 : memoryCostOneAt 13=.return (.rstruct
 [.op .sub [.var .local (ofString "ca"),.var .local (ofString "cb")],
  .op .sub [.var .local (ofString "after"),.var .local (ofString "before")]]) := rfl
#print axioms source_memory_cost_one_9
#print axioms source_memory_cost_one_13
end InitECandidate.Runtime
