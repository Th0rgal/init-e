import InitECandidate.Runtime.GuestCostStackPush
import InitECandidate.Runtime.GuestCostU256Add
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

variable {F : Type}

set_option maxHeartbeats 4000000

/-- The pinned installed body of the `op_add` arm: two pops, the gas charge, the
four-limb add, the push of its result, the program-counter increment and zero. -/
noncomputable def opAddSpine : ProgHOL 64 :=
  .decCall (ofString "x") comb4Shape (ofString "stack_pop") []
    (.decCall (ofString "y") comb4Shape (ofString "stack_pop") []
      (.seq
        (.call (some (none, none)) (ofString "charge_gas")
          [(.const (3 : BitVec 64))])
        (.decCall (ofString "r") comb4Shape (ofString "u256_add")
          [(.var VarKind.local (ofString "x")), (.var VarKind.local (ofString "y"))]
          (.seq
            (.call (some (none, none)) (ofString "stack_push")
              [(.var VarKind.local (ofString "r"))])
            (.seq
              (.call (some (none, none)) (ofString "pc_add")
                [(.const (1 : BitVec 64))])
              (.return (.const (0 : BitVec 64))))))))

theorem source_opAdd_body :
    sourceFunctionBody Guest.guestFn_op_add = opAddSpine := by
  cbv

#print axioms source_opAdd_body

end InitECandidate.Runtime.FineCost
