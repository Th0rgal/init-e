import InitECandidate.Runtime.GuestCostOpPopBody
namespace InitECandidate.Runtime.FineCost
open Flapjack Flapjack.Pancake.PanLang Flapjack.PanSemStateFiniteExact
open Flapjack.Basis.Pure.MlString

set_option maxHeartbeats 4000000

/-- Actual `op_lt` body: pop x, pop y, charge three gas, compute `u256_lt`,
push the boolean, advance pc and return. -/
theorem source_opLt_body :
    sourceFunctionBody Guest.guestFn_op_lt =
      .decCall (ofString "x") comb4Shape (ofString "stack_pop") []
        (.decCall (ofString "y") comb4Shape (ofString "stack_pop") []
          (.seq (.call (some (none, none)) (ofString "charge_gas")
              [.const (3 : BitVec 64)])
            (.decCall (ofString "r") .one (ofString "u256_lt")
              [.var VarKind.local (ofString "x"), .var VarKind.local (ofString "y")]
              (.seq (.call (some (none, none)) (ofString "stack_push_bool")
                  [.var VarKind.local (ofString "r")])
                (.seq (.call (some (none, none)) (ofString "pc_add")
                    [.const (1 : BitVec 64)])
                  (.return (.const (0 : BitVec 64)))))))) := by
  cbv

/-- Actual `op_gt` body: same shape with `u256_gt`. -/
theorem source_opGt_body :
    sourceFunctionBody Guest.guestFn_op_gt =
      .decCall (ofString "x") comb4Shape (ofString "stack_pop") []
        (.decCall (ofString "y") comb4Shape (ofString "stack_pop") []
          (.seq (.call (some (none, none)) (ofString "charge_gas")
              [.const (3 : BitVec 64)])
            (.decCall (ofString "r") .one (ofString "u256_gt")
              [.var VarKind.local (ofString "x"), .var VarKind.local (ofString "y")]
              (.seq (.call (some (none, none)) (ofString "stack_push_bool")
                  [.var VarKind.local (ofString "r")])
                (.seq (.call (some (none, none)) (ofString "pc_add")
                    [.const (1 : BitVec 64)])
                  (.return (.const (0 : BitVec 64)))))))) := by
  cbv

#print axioms source_opLt_body
#print axioms source_opGt_body
end InitECandidate.Runtime.FineCost
